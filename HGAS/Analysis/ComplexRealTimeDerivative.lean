import Mathlib.Analysis.Complex.RealDeriv

/-!
# Realifying complex-valued trajectories

Polynomial compilers represent one complex coordinate by two real
coordinates.  The elementary lemmas in this file are the reusable
calculus bridge: a complex-valued function of real time may be
differentiated first, and then its real and imaginary parts may be
extracted.

The proof deliberately passes through Fréchet derivatives.  The maps
`Complex.reCLM` and `Complex.imCLM` are continuous real-linear maps, so
the ordinary chain rule applies without any holomorphicity hypothesis.
-/

namespace HGAS

noncomputable section

/-- Take the real part of a complex-valued real-time derivative. -/
theorem HasDerivAt.complex_re
    {f : ℝ → ℂ} {f' : ℂ} {t : ℝ}
    (hf : HasDerivAt f f' t) :
    HasDerivAt
      (fun u => (f u).re) f'.re t := by
  have h :=
    Complex.reCLM.hasFDerivAt.comp t hf.hasFDerivAt
  rw [hasFDerivAt_iff_hasDerivAt] at h
  simpa only [Function.comp_apply,
    Complex.reCLM_apply,
    ContinuousLinearMap.coe_comp',
    ContinuousLinearMap.toSpanSingleton_apply_one] using h

/-- Take the imaginary part of a complex-valued real-time derivative. -/
theorem HasDerivAt.complex_im
    {f : ℝ → ℂ} {f' : ℂ} {t : ℝ}
    (hf : HasDerivAt f f' t) :
    HasDerivAt
      (fun u => (f u).im) f'.im t := by
  have h :=
    Complex.imCLM.hasFDerivAt.comp t hf.hasFDerivAt
  rw [hasFDerivAt_iff_hasDerivAt] at h
  simpa only [Function.comp_apply,
    Complex.imCLM_apply,
    ContinuousLinearMap.coe_comp',
    ContinuousLinearMap.toSpanSingleton_apply_one] using h

end

end HGAS
