# Formalization progress

Status: `open` | `wip` | `sorry` | `done`. Blueprint: [`formalization_dag.md`](formalization_dag.md).

## Wave 1 (complete)

| Node | Module | Status | Notes |
| --- | --- | --- | --- |
| N01–N02 | `BN.Definition` | done | already in tree |
| N03–N05, N11 | `BN.Basic.Spectrum` | done | `BN/Basic/Spectrum.lean` |
| SP13–SP17 | `BN.Spectral.Interlace` | done | `BN/Spectral/Interlace.lean` |
| CP06–CP07 | `BN.CP.Closed` | done | `BN/CP/Closed.lean` |
| EL01, EL07 | `BN.M.Elim` | done | `BN/M/Elim.lean` |
| EL08–EL09 | `BN.M.Elim` | done | `BN/M/Elim.lean` |
| EL02–EL03 | `BN.M.Elim` | done | `BN/M/Elim.lean` |
| EL04–EL06 | `BN.M.Elim` | done | diagonal expansion / cofactor / `s`,`ρ` |
| SP01–SP03 | `BN.Spectral.Perron` | done | `BN/Spectral/Perron.lean` |
| SP04–SP06, SP09–SP10 | `BN.Spectral.Weighted` | done | `BN/Spectral/Weighted.lean` |
| CG04 | `BN.Spectral.Gram` | done | `BN/Spectral/Gram.lean` |
| CG06–CG07 | `BN.Spectral.Conic` | done | `BN/Spectral/Conic.lean` |
| CG09 | `BN.Spectral.Conic` | done | `ω ≤ chiVec3` |
| CP08–CP11 | `BN.CP.Pair` | done | `BN/CP/Pair.lean` |
| HP01, HP03 | `BN.M.HalfPlane` | done | `BN/M/HalfPlane.lean` |
| SC08 | `BN.M.Schur` | done | `BN/M/Schur.lean` |
| HP07 | `BN.M.HalfPlane` | done | `BN/M/HalfPlane.lean` |
| HP02 | `BN.M.HalfPlane` | done | unique minimizer → MX06 |
| N06–N10, N14 | `BN.Basic.Inner` | done | `BN/Basic/Inner.lean` |
| MS01–MS07 | `BN.MS.Basic` | done | `BN/MS/Basic.lean` |
| N12–N13 | `BN.Basic.Graph` | done | `BN/Basic/Graph.lean` |
| KR01–KR06 | `BN.Kernel.Data` | done | `BN/Kernel/Data.lean` |
| KR07 | `BN.Kernel.SM` | done | `BN/Kernel/SM.lean` |
| KR08–KR13 | `BN.Kernel.Bilinear` | done | `BN/Kernel/Bilinear.lean` |
| KR18–KR25 | `BN.Kernel.N` | done | `BN/Kernel/N.lean` |
| KR26–KR27 | `BN.Kernel.Main` | done | `BN/Kernel/Main.lean` |
| CG01–CG03 | `BN.Spectral.Variational` | done | `BN/Spectral/Variational.lean` |
| CP01–CP05 | `BN.CP.Basic` | done | `BN/CP/Basic.lean` |
| TN01–TN04 | `BN.TN.Basic` | done | `BN/TN/Basic.lean` |
| TN14–TN17 | `BN.TN.Convex` | done | `BN/TN/Convex.lean` |
| KR14–KR17 | `BN.Kernel.Signs` | done | `BN/Kernel/Signs.lean` |
| MX01–MX05 | `BN.M.Basic` | done | `BN/M/Basic.lean` |
| MX06–MX09 | `BN.M.Config` | done | `BN/M/Config.lean` |
| SC01–SC07 | `BN.M.Schur` | done | `q`, `γ`, `F`, `L`, `L_EE` |
| SC10–SC12, SC14–SC16 | `BN.M.Schur` | done | `𝒰` rows / `L_red` Laplacian |
| SC19–SC20 | `BN.M.GammaZero` | done | `BN/M/GammaZero.lean` |
| TN05–TN10 | `BN.TN.Truncated` | done | `BN/TN/Truncated.lean` |
| TN11–TN12 | `BN.TN.Truncated` | done | chambers / staircase |
| TN13 | `BN.TN.Truncated` | done | `isTotallyNonneg_truncatedSquare` |
| EL10–EL14 | `BN.M.Elim` | done | `lem_elimination` |
| SC09, SC13, SC17–SC18 | `BN.M.Schur` | done | `isCompletelyPositive_M_Xconfig` |
| SC21 | `BN.M.GammaZero` | done | `γ=0` / `p=0` CP |
| HP04–HP06, HP08 | `BN.M.HalfPlane` / `BN.M.Main` | done | `thm:matrix` |
| SP07–SP12 | `BN.Spectral.Weighted` | done | `thm:weighted` |
| SP18 | `BN.Main` | done | `conj:BN` |
| CG05 | `BN.Spectral.Gram` | done | `thm:gram` (`gram_le`) |
| CG08, CG10 | `BN.Spectral.Conic` | done | `cor:parameter` (`chiVec3_eq_cliqueNum`) |

Remaining catalog nodes: none. Public target `conj:BN` and `cor:parameter` are both `done`.
