import HGAS.Lyapunov.RationalCertificateEnumeration
import Mathlib.Tactic

/-!
# Radial SOS algebra for rational Lyapunov certificates

This file isolates the elementary algebra needed by the Reznick route to
completeness of the rational Lyapunov search.

There are two independent facts behind that route.

1. Products of sums of rational squares are again sums of rational squares.
   Since

   ```
   ρ = X₁² + ... + Xₙ²,
   ```

   multiplying a strict homogeneous SOS margin by any power of `ρ`
   preserves such a margin.

2. Multiplying the numerator and denominator of

   ```
   V = p / ρ^r
   ```

   by the same radial power does not change `V`.  More precisely, its
   polynomial decay numerator satisfies the exact identity

   ```
   q(F, ρ^s p, r+s) = ρ^s q(F,p,r).
   ```

Consequently separate radial SOS multipliers for the value and decay forms
can be synchronized.  The module also supplies the finite-code bridge:
semantic rational margin certificates can be assembled into one candidate
accepted by `checkRationalLyapunov`.

No Positivstellensatz is assumed or postulated here.  The remaining deep
statement on this route is precisely a strict Reznick theorem saying that
every positive-definite rational form admits a radial strict-SOS witness.
Keeping that statement outside this module makes the trusted boundary
explicit and leaves all algebra below reusable.
-/

namespace HGAS

open MvPolynomial
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-! ## Products of finite SOS certificates -/

namespace SOSCertificate

/-- The product of two finite sums of rational squares is again a finite
sum of rational squares.

The new square roots are all pairwise products of old square roots.  The
equivalence `Fin m × Fin l ≃ Fin (m*l)` merely flattens the pair of finite
indices into the certificate format used by `SOSCertificate`. -/
def mul
    {p q : MvPolynomial (Fin n) ℚ}
    (cp : SOSCertificate p) (cq : SOSCertificate q) :
    SOSCertificate (p * q) where
  numSquares := cp.numSquares * cq.numSquares
  square k :=
    cp.square (finProdFinEquiv.symm k).1 *
      cq.square (finProdFinEquiv.symm k).2
  identity := by
    calc
      p * q =
          (∑ i, cp.square i ^ 2) * (∑ j, cq.square j ^ 2) :=
        congrArg₂ (· * ·) cp.identity cq.identity
      _ =
          ∑ z : Fin cp.numSquares × Fin cq.numSquares,
            (cp.square z.1 * cq.square z.2) ^ 2 := by
        rw [Finset.sum_mul]
        simp_rw [Finset.mul_sum]
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro i _hi
        apply Finset.sum_congr rfl
        intro j _hj
        ring
      _ = ∑ k : Fin (cp.numSquares * cq.numSquares),
          (cp.square (finProdFinEquiv.symm k).1 *
            cq.square (finProdFinEquiv.symm k).2) ^ 2 := by
        exact Fintype.sum_equiv finProdFinEquiv _ _ (fun z ↦ by simp)

end SOSCertificate

/-! ## Homogeneous SOS certificates and the radial form -/

/-- An SOS representation whose square roots all have the same degree.

This small wrapper is useful independently of strict margins: it records
exactly the extra invariant needed when multiplying homogeneous SOS
identities. -/
structure HomogeneousSOSCertificate
    (p : MvPolynomial (Fin n) ℚ) (rootDegree : ℕ) where
  sos : SOSCertificate p
  square_homogeneous :
    ∀ i, (sos.square i).IsHomogeneous rootDegree

namespace HomogeneousSOSCertificate

/-- Transport a homogeneous SOS certificate across an exact polynomial
identity. -/
def congrTarget
    {p q : MvPolynomial (Fin n) ℚ} {k : ℕ}
    (c : HomogeneousSOSCertificate p k) (h : p = q) :
    HomogeneousSOSCertificate q k := by
  subst q
  exact c

/-- The constant polynomial one is one homogeneous square. -/
def one :
    HomogeneousSOSCertificate (1 : MvPolynomial (Fin n) ℚ) 0 where
  sos :=
    { numSquares := 1
      square := fun _ ↦ 1
      identity := by simp }
  square_homogeneous := fun _ ↦ isHomogeneous_one (Fin n) ℚ

/-- Multiplication preserves homogeneous SOS certificates and adds the
degrees of their square roots. -/
def mul
    {p q : MvPolynomial (Fin n) ℚ} {k l : ℕ}
    (cp : HomogeneousSOSCertificate p k)
    (cq : HomogeneousSOSCertificate q l) :
    HomogeneousSOSCertificate (p * q) (k + l) where
  sos := cp.sos.mul cq.sos
  square_homogeneous := by
    intro z
    exact
      (cp.square_homogeneous (finProdFinEquiv.symm z).1).mul
        (cq.square_homogeneous (finProdFinEquiv.symm z).2)

/-- The radial form `ρ` is the sum of the squares of the coordinate
variables, with homogeneous square roots of degree one. -/
def rho :
    HomogeneousSOSCertificate (rhoPolynomial (n := n)) 1 where
  sos :=
    { numSquares := n
      square := fun i ↦ X i
      identity := by rfl }
  square_homogeneous := fun i ↦ isHomogeneous_X ℚ i

end HomogeneousSOSCertificate

namespace StrictHomogeneousMarginCertificate

/-- Transport a strict margin certificate across exact target and degree
identities. -/
def congr
    {p q : MvPolynomial (Fin n) ℚ} {k l : ℕ}
    (cert : StrictHomogeneousMarginCertificate p k)
    (hpq : p = q) (hkl : k = l) :
    StrictHomogeneousMarginCertificate q l := by
  subst q
  subst l
  exact cert

/-- Forget the distinguished positive margin while retaining its
homogeneous SOS identity. -/
def toHomogeneousSOS
    {p : MvPolynomial (Fin n) ℚ} {k : ℕ}
    (cert : StrictHomogeneousMarginCertificate p k) :
    HomogeneousSOSCertificate
      (p - C cert.epsilon * rhoPolynomial ^ k) k where
  sos := cert.sos
  square_homogeneous := cert.square_homogeneous

/-- One radial multiplication preserves a strict homogeneous SOS margin.

If `p - ερ^k` is SOS, then

```
ρp - ερ^(k+1) = ρ (p - ερ^k)
```

is SOS by the product construction above. -/
def radialMulOne
    {p : MvPolynomial (Fin n) ℚ} {k : ℕ}
    (cert : StrictHomogeneousMarginCertificate p k) :
    StrictHomogeneousMarginCertificate
      (rhoPolynomial * p) (k + 1) := by
  let product :=
    HomogeneousSOSCertificate.mul cert.toHomogeneousSOS
      (HomogeneousSOSCertificate.rho (n := n))
  have htarget :
      (p - C cert.epsilon * rhoPolynomial ^ k) * rhoPolynomial =
        rhoPolynomial * p -
          C cert.epsilon * rhoPolynomial ^ (k + 1) := by
    rw [pow_succ]
    ring
  let target :=
    HomogeneousSOSCertificate.congrTarget product htarget
  exact
    { epsilon := cert.epsilon
      epsilon_pos := cert.epsilon_pos
      sos := target.sos
      square_homogeneous := target.square_homogeneous }

/-- Multiplication by an arbitrary radial power preserves a strict
homogeneous SOS margin. -/
theorem exists_radialMul
    {p : MvPolynomial (Fin n) ℚ} {k : ℕ}
    (cert : StrictHomogeneousMarginCertificate p k) (s : ℕ) :
    Nonempty
      (StrictHomogeneousMarginCertificate
        (rhoPolynomial ^ s * p) (k + s)) := by
  induction s with
  | zero =>
      simpa using Nonempty.intro cert
  | succ s ih =>
      obtain ⟨cs⟩ := ih
      refine ⟨?_⟩
      simpa [pow_succ, Nat.add_assoc, mul_assoc, mul_comm, mul_left_comm]
        using radialMulOne cs

end StrictHomogeneousMarginCertificate

/-! ## Exact radial scaling of the decay numerator -/

/-- The partial derivative of `ρ` is `2Xᵢ`. -/
theorem pderiv_rhoPolynomial (i : Fin n) :
    pderiv i (rhoPolynomial (n := n)) =
      C (2 : ℚ) * X i := by
  classical
  have hderiv :
      pderiv i (rhoPolynomial (n := n)) =
        (2 : MvPolynomial (Fin n) ℚ) * X i := by
    simp [rhoPolynomial, Pi.single_apply]
  have hconstant :
      (2 : MvPolynomial (Fin n) ℚ) = C (2 : ℚ) :=
    (map_ofNat (C : ℚ →+* MvPolynomial (Fin n) ℚ) 2).symm
  rw [hderiv, hconstant]

/-- The partial derivative of a radial power is the usual power rule. -/
theorem pderiv_rhoPolynomial_pow (i : Fin n) (s : ℕ) :
    pderiv i ((rhoPolynomial (n := n)) ^ s) =
      C (2 * (s : ℚ)) * rhoPolynomial ^ (s - 1) * X i := by
  rw [pderiv_pow, pderiv_rhoPolynomial]
  rw [show (s : MvPolynomial (Fin n) ℚ) = C (s : ℚ) by
    exact (map_natCast (C : ℚ →+* MvPolynomial (Fin n) ℚ) s).symm]
  rw [map_mul]
  norm_num
  ring

/-- Product rule for `∇(ρ^s p)·F`, arranged into radial and non-radial
parts. -/
theorem gradientDotField_rho_pow_mul
    (F : PolynomialField n)
    (p : MvPolynomial (Fin n) ℚ) (s : ℕ) :
    gradientDotField (rhoPolynomial ^ s * p) F =
      rhoPolynomial ^ s * gradientDotField p F +
        C (2 * (s : ℚ)) * rhoPolynomial ^ (s - 1) * p *
          radialDotPolynomial F := by
  classical
  unfold gradientDotField radialDotPolynomial
  simp_rw [pderiv_mul, pderiv_rhoPolynomial_pow]
  calc
    ∑ i, ((C (2 * (s : ℚ)) * rhoPolynomial ^ (s - 1) * X i) * p +
          rhoPolynomial ^ s * pderiv i p) * F i =
        ∑ i, ((C (2 * (s : ℚ)) * rhoPolynomial ^ (s - 1) * p) *
            (X i * F i) +
          rhoPolynomial ^ s * (pderiv i p * F i)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = (C (2 * (s : ℚ)) * rhoPolynomial ^ (s - 1) * p) *
          (∑ i, X i * F i) +
        rhoPolynomial ^ s * (∑ i, pderiv i p * F i) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = rhoPolynomial ^ s * (∑ i, pderiv i p * F i) +
        C (2 * (s : ℚ)) * rhoPolynomial ^ (s - 1) * p *
          (∑ i, X i * F i) := by ring

/-- Simultaneous radial multiplication of the Lyapunov numerator and
denominator multiplies the decay numerator by exactly the same radial
power:

```
q(F, ρ^s p, r+s) = ρ^s q(F,p,r).
```

This cancellation is the central algebraic reason why two independently
obtained Reznick exponents can later be synchronized. -/
theorem rationalLyapunovNumerator_rho_pow_mul
    (F : PolynomialField n)
    (p : MvPolynomial (Fin n) ℚ) (r s : ℕ) :
    rationalLyapunovNumerator F (rhoPolynomial ^ s * p) (r + s) =
      rhoPolynomial ^ s * rationalLyapunovNumerator F p r := by
  cases s with
  | zero =>
      simp
  | succ s =>
      rw [rationalLyapunovNumerator, rationalLyapunovNumerator,
        gradientDotField_rho_pow_mul]
      simp only [Nat.succ_sub_one, pow_succ]
      push_cast
      simp only [map_add, map_mul, map_ofNat, map_natCast]
      ring

/-! ## From semantic certificates to the executable checker -/

/-- A semantic strict-margin certificate can be encoded against any sparse
target code which decodes to its target polynomial.

The existing canonical theorem uses `PolynomialCode.encode p`.  This
version is essential for the decay numerator, whose checker target is
produced by the executable differentiation compiler and need not be
syntactically the canonical encoding. -/
theorem checkStrictMargin_of_certificate_eq
    (target : PolynomialCode n) (k : ℕ)
    {p : MvPolynomial (Fin n) ℚ}
    (cert : StrictHomogeneousMarginCertificate p k)
    (hdecode : PolynomialCode.decode target = p) :
    checkStrictMargin target k
      (strictMarginCodeOfCertificate cert) = true := by
  subst p
  rw [checkStrictMargin_eq_true_iff]
  refine ⟨by
    simpa [strictMarginCodeOfCertificate] using cert.epsilon_pos, ?_, ?_⟩
  · intro s hs
    simp only [strictMarginCodeOfCertificate] at hs
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hs
    simpa using cert.square_homogeneous i
  · simp only [strictMarginCodeOfCertificate]
    rw [RationalCode.decode_encode]
    calc
      PolynomialCode.decode target -
          C cert.epsilon * rhoPolynomial ^ k =
          ∑ i, cert.sos.square i ^ 2 :=
        cert.sos.identity
      _ = ((List.ofFn fun i ↦
          PolynomialCode.encode (cert.sos.square i)).map
            fun s ↦ PolynomialCode.decode s ^ 2).sum := by
        simp only [List.map_ofFn, List.sum_ofFn,
          Function.comp_apply, PolynomialCode.decode_encode]

/-- Assemble value and decay margin certificates into the finite product
format consumed by `checkRationalLyapunov`. -/
def rationalLyapunovCandidateOfCertificates
    (F : PolynomialFieldCode n)
    (p : MvPolynomial (Fin n) ℚ) (r k : ℕ)
    (valueCert : StrictHomogeneousMarginCertificate p (r + 1))
    (decayCert :
      StrictHomogeneousMarginCertificate
        (rationalLyapunovNumerator
          (PolynomialFieldCode.decode F) p r) k) :
    RationalLyapunovCandidate n :=
  ((r, PolynomialCode.encode p),
    (strictMarginCodeOfCertificate valueCert,
      (k, strictMarginCodeOfCertificate decayCert)))

/-- The candidate assembled from two exact semantic certificates is
accepted by the executable checker. -/
theorem check_rationalLyapunovCandidateOfCertificates
    (F : PolynomialFieldCode n)
    (p : MvPolynomial (Fin n) ℚ) (r k : ℕ)
    (valueCert : StrictHomogeneousMarginCertificate p (r + 1))
    (decayCert :
      StrictHomogeneousMarginCertificate
        (rationalLyapunovNumerator
          (PolynomialFieldCode.decode F) p r) k)
    (hrk : r + 1 ≤ k) :
    checkRationalLyapunov F
      (rationalLyapunovCandidateOfCertificates
        F p r k valueCert decayCert) = true := by
  rw [checkRationalLyapunov_eq_true_iff]
  refine ⟨?_, hrk, ?_⟩
  · change
      checkStrictMargin (PolynomialCode.encode p) (r + 1)
        (strictMarginCodeOfCertificate valueCert) = true
    exact checkStrictMargin_of_certificate_eq
      (PolynomialCode.encode p) (r + 1) valueCert
      (PolynomialCode.decode_encode p)
  · let target :=
      PolynomialCode.rationalLyapunovNumerator
        F (PolynomialCode.encode p) r
    have hdecode :
        PolynomialCode.decode target =
          rationalLyapunovNumerator
            (PolynomialFieldCode.decode F) p r := by
      simp [target]
    change
      checkStrictMargin target k
        (strictMarginCodeOfCertificate decayCert) = true
    exact checkStrictMargin_of_certificate_eq
      target k decayCert hdecode

/-- Two semantic strict margins imply existence of an accepted finite
rational Lyapunov candidate. -/
theorem hasCheckedRationalLyapunov_of_certificates
    (F : PolynomialFieldCode n)
    (p : MvPolynomial (Fin n) ℚ) (r k : ℕ)
    (valueCert : StrictHomogeneousMarginCertificate p (r + 1))
    (decayCert :
      StrictHomogeneousMarginCertificate
        (rationalLyapunovNumerator
          (PolynomialFieldCode.decode F) p r) k)
    (hrk : r + 1 ≤ k) :
    HasCheckedRationalLyapunov F :=
  ⟨rationalLyapunovCandidateOfCertificates F p r k valueCert decayCert,
    check_rationalLyapunovCandidateOfCertificates
      F p r k valueCert decayCert hrk⟩

/-! ## Synchronizing separate radial multipliers -/

/-- A radial strict-SOS witness for a form `p` of degree `2k`.

The witness records an exponent `s` and a strict margin certificate for
`ρ^s p`, whose square roots have degree `k+s`.  This is exactly the output
needed from a strict form of Reznick's theorem. -/
structure RadialStrictSOSWitness
    (p : MvPolynomial (Fin n) ℚ) (k : ℕ) where
  exponent : ℕ
  certificate :
    StrictHomogeneousMarginCertificate
      (rhoPolynomial ^ exponent * p) (k + exponent)

/-- Separate radial strict-SOS witnesses for the Lyapunov value form and
its decay form can always be synchronized.

If the two Reznick exponents are `a` and `b`, multiply the value identity
by `ρ^b` and the decay identity by `ρ^a`.  Both then use the common
exponent `a+b`.  The exact decay-numerator scaling theorem above shows that
the synchronized decay certificate is a certificate for the new rational
Lyapunov representation, not merely for an unrelated polynomial. -/
theorem hasCheckedRationalLyapunov_of_radialStrictSOS
    (F : PolynomialFieldCode n)
    (p : MvPolynomial (Fin n) ℚ) (r k : ℕ)
    (hrk : r + 1 ≤ k)
    (valueWitness : RadialStrictSOSWitness p (r + 1))
    (decayWitness :
      RadialStrictSOSWitness
        (rationalLyapunovNumerator
          (PolynomialFieldCode.decode F) p r) k) :
    HasCheckedRationalLyapunov F := by
  let a := valueWitness.exponent
  let b := decayWitness.exponent
  let s := a + b
  let p' := rhoPolynomial ^ s * p
  let r' := r + s
  let k' := k + s
  obtain ⟨valueExtended⟩ :=
    valueWitness.certificate.exists_radialMul b
  have hvalueTarget :
      rhoPolynomial ^ b * (rhoPolynomial ^ a * p) = p' := by
    simp only [p', s]
    rw [← mul_assoc, ← pow_add]
    congr 2
    omega
  have hvalueDegree :
      (r + 1 + a) + b = r' + 1 := by
    simp only [r', s]
    omega
  let valueCert :
      StrictHomogeneousMarginCertificate p' (r' + 1) :=
    valueExtended.congr hvalueTarget hvalueDegree
  obtain ⟨decayExtended⟩ :=
    decayWitness.certificate.exists_radialMul a
  have hdecayTarget :
      rhoPolynomial ^ a *
          (rhoPolynomial ^ b *
            rationalLyapunovNumerator
              (PolynomialFieldCode.decode F) p r) =
        rationalLyapunovNumerator
          (PolynomialFieldCode.decode F) p' r' := by
    calc
      rhoPolynomial ^ a *
          (rhoPolynomial ^ b *
            rationalLyapunovNumerator
              (PolynomialFieldCode.decode F) p r) =
          rhoPolynomial ^ s *
            rationalLyapunovNumerator
              (PolynomialFieldCode.decode F) p r := by
        simp only [s]
        rw [pow_add]
        ring
      _ = rationalLyapunovNumerator
          (PolynomialFieldCode.decode F) p' r' := by
        exact
          (rationalLyapunovNumerator_rho_pow_mul
            (PolynomialFieldCode.decode F) p r s).symm
  have hdecayDegree :
      (k + b) + a = k' := by
    simp only [k', s]
    omega
  let decayCert :
      StrictHomogeneousMarginCertificate
        (rationalLyapunovNumerator
          (PolynomialFieldCode.decode F) p' r') k' :=
    decayExtended.congr hdecayTarget hdecayDegree
  apply hasCheckedRationalLyapunov_of_certificates
    F p' r' k' valueCert decayCert
  simp only [r', k', s]
  omega

/-- The single deep completeness property remaining on the SOS route.

This is deliberately only a named proposition: clients may prove it from
a formal Reznick theorem or supply it for a restricted class of forms. -/
def StrictReznickProperty (n : ℕ) : Prop :=
  ∀ (p : MvPolynomial (Fin n) ℚ) (k : ℕ),
    p.IsHomogeneous (2 * k) →
    (∀ x : Fin n → ℝ, x ≠ 0 → 0 < ratMvPolynomialEval p x) →
      Nonempty (RadialStrictSOSWitness p k)

/-- Once `StrictReznickProperty` is available, two positive-definite
homogeneous forms give an accepted rational Lyapunov certificate.  This
theorem makes the external theorem boundary of the SOS route exact. -/
theorem hasCheckedRationalLyapunov_of_strictReznick
    (hReznick : StrictReznickProperty n)
    (F : PolynomialFieldCode n)
    (p : MvPolynomial (Fin n) ℚ) (r k : ℕ)
    (hp : p.IsHomogeneous (2 * (r + 1)))
    (hvaluePos :
      ∀ x : Fin n → ℝ, x ≠ 0 → 0 < ratMvPolynomialEval p x)
    (hq :
      (rationalLyapunovNumerator
        (PolynomialFieldCode.decode F) p r).IsHomogeneous (2 * k))
    (hdecayPos :
      ∀ x : Fin n → ℝ, x ≠ 0 →
        0 < ratMvPolynomialEval
          (rationalLyapunovNumerator
            (PolynomialFieldCode.decode F) p r) x)
    (hrk : r + 1 ≤ k) :
    HasCheckedRationalLyapunov F := by
  obtain ⟨valueWitness⟩ :=
    hReznick p (r + 1) hp hvaluePos
  obtain ⟨decayWitness⟩ :=
    hReznick
      (rationalLyapunovNumerator
        (PolynomialFieldCode.decode F) p r)
      k hq hdecayPos
  exact hasCheckedRationalLyapunov_of_radialStrictSOS
    F p r k hrk valueWitness decayWitness

end

end HGAS
