#!/usr/bin/env ruby
# frozen_string_literal: true

# Cross-checks the axiom report of the compared theorems against the metadata.
#
# For every theorem in comparator.json `theorem_names`, runs `#print axioms` in the
# environment of the solution module and requires that the reported axioms are
# exactly (as sets)
#   * comparator.json `permitted_axioms`,
#   * formalization.yaml `status.axioms`, and
#   * formalization.yaml `status.main_results[].axioms` for that declaration.
# It also fails if any theorem depends on `sorryAx`.  Palomar rejected a submission
# whose `status.axioms` had been left empty; this makes the metadata mechanically
# tied to what Lean actually reports.
#
# Usage: ruby scripts/check-axioms.rb [repository-root]
# Requires `lake` on PATH and the solution module to be buildable (it is built here).

require "json"
require "yaml"
require "open3"

root = File.expand_path(ARGV.fetch(0, File.join(__dir__, "..")))
comparator = JSON.parse(File.read(File.join(root, "comparator.json"), encoding: "UTF-8"))
meta = YAML.safe_load(File.read(File.join(root, "formalization.yaml"), encoding: "UTF-8"), aliases: false)

solution = comparator.fetch("solution_module")
names = comparator.fetch("theorem_names")
permitted = comparator.fetch("permitted_axioms").sort
status = meta.fetch("status")
declared = Array(status["axioms"]).sort
per_result = Array(status["main_results"]).each_with_object({}) do |r, h|
  h[r["declaration"]] = Array(r["axioms"]).sort if r.is_a?(Hash)
end

Dir.chdir(root) do
  system("lake", "build", solution, exception: true)
  script = "import #{solution}\n" + names.map { |n| "#print axioms #{n}\n" }.join
  out, err, st = Open3.capture3("lake", "env", "lean", "--stdin", stdin_data: script)
  unless st.success?
    warn out, err
    abort "error: lean failed while printing axioms"
  end

  errors = []
  reported = {}
  out.each_line do |line|
    if (m = line.match(/\A'([^']+)' depends on axioms: \[([^\]]*)\]/))
      reported[m[1]] = m[2].split(",").map(&:strip).reject(&:empty?).sort
    elsif (m = line.match(/\A'([^']+)' does not depend on any axioms/))
      reported[m[1]] = []
    end
  end

  names.each do |n|
    axioms = reported[n]
    if axioms.nil?
      errors << "no axiom report for #{n} (lean output: #{out.strip.inspect})"
      next
    end
    puts "#{n}: #{axioms.join(", ")}"
    errors << "#{n} depends on sorryAx" if axioms.include?("sorryAx")
    errors << "#{n} uses #{axioms.inspect}, not comparator.json permitted_axioms #{permitted.inspect}" unless axioms == permitted
    errors << "#{n} uses #{axioms.inspect}, but formalization.yaml status.axioms is #{declared.inspect}" unless axioms == declared
    if per_result.key?(n)
      errors << "#{n} uses #{axioms.inspect}, but its status.main_results entry lists #{per_result[n].inspect}" unless axioms == per_result[n]
    else
      errors << "#{n} has no status.main_results entry in formalization.yaml"
    end
  end

  if errors.empty?
    puts "axiom reports agree with comparator.json and formalization.yaml"
  else
    errors.each { |e| warn "error: #{e}" }
    exit 1
  end
end
