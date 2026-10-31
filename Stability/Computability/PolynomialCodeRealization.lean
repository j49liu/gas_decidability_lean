import Stability.Computability.RawPolynomialStatistics

/-!
# Exact polynomial statistics under coordinate reindexing

Bijective variable renaming preserves degree and coefficient mass and commutes
with partial differentiation. The fixed-dimensional code operations below
compute these semantic statistics, including cancellation of repeated terms.
-/

namespace Stability.PolynomialCodeRealization

open HGAS

variable {σ τ : Type*}

theorem totalDegree_rename_equiv (e : σ ≃ τ) (p : MvPolynomial σ ℚ) :
    (MvPolynomial.rename e p).totalDegree = p.totalDegree :=
  MvPolynomial.totalDegree_renameEquiv e p

theorem coefficientMass_rename_injective {f : σ → τ} (hf : Function.Injective f)
    (p : MvPolynomial σ ℚ) :
    Simulation.AbsFormula.coefficientMass (MvPolynomial.rename f p) =
      Simulation.AbsFormula.coefficientMass p := by
  classical
  unfold Simulation.AbsFormula.coefficientMass
  rw [MvPolynomial.support_rename_of_injective hf, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro d _
    rw [MvPolynomial.coeff_rename_mapDomain f hf]
  · intro a _ b _ hab
    exact Finsupp.mapDomain_injective hf hab

theorem coefficientMass_rename_equiv (e : σ ≃ τ) (p : MvPolynomial σ ℚ) :
    Simulation.AbsFormula.coefficientMass (MvPolynomial.rename e p) =
      Simulation.AbsFormula.coefficientMass p :=
  coefficientMass_rename_injective e.injective p

theorem pderiv_rename_equiv (e : σ ≃ τ) (i : σ) (p : MvPolynomial σ ℚ) :
    MvPolynomial.pderiv (e i) (MvPolynomial.rename e p) =
      MvPolynomial.rename e (MvPolynomial.pderiv i p) :=
  MvPolynomial.pderiv_rename e.injective i p

theorem coeff_rename_equiv (e : σ ≃ τ) (p : MvPolynomial σ ℚ) (d : σ →₀ ℕ) :
    (MvPolynomial.rename e p).coeff (d.mapDomain e) = p.coeff d :=
  MvPolynomial.coeff_rename_mapDomain e e.injective p d

theorem rename_equiv_injective (e : σ ≃ τ) :
    Function.Injective (MvPolynomial.rename e : MvPolynomial σ ℚ → MvPolynomial τ ℚ) :=
  (MvPolynomial.renameEquiv ℚ e).injective

theorem rename_equiv_sum {ι : Type*} (e : σ ≃ τ) (s : Finset ι)
    (p : ι → MvPolynomial σ ℚ) :
    MvPolynomial.rename e (∑ i ∈ s, p i) = ∑ i ∈ s, MvPolynomial.rename e (p i) :=
  map_sum (MvPolynomial.rename e) p s

theorem rename_equiv_sum_univ [Fintype σ] [Fintype τ] (e : σ ≃ τ)
    (p : σ → MvPolynomial σ ℚ) :
    MvPolynomial.rename e (∑ i, p i) =
      ∑ j, MvPolynomial.rename e (p (e.symm j)) := by
  rw [map_sum]
  exact Fintype.sum_equiv e (fun i ↦ MvPolynomial.rename e (p i))
    (fun j ↦ MvPolynomial.rename e (p (e.symm j))) (fun i ↦ by simp)

/-- The collected-coefficient cube bound is exactly the rational coefficient mass. -/
theorem decode_cubeAbsBoundCode {n : ℕ} (p : PolynomialCode n) :
    RationalCode.decode (PolynomialCode.cubeAbsBoundCode p) =
      Simulation.AbsFormula.coefficientMass (PolynomialCode.decode p) := by
  simpa only [RawPolynomialCode.cubeAbsBoundCode_ofFixed] using
    RawPolynomialCode.cubeAbsBoundCode_eq_coefficientMass p

/-- Exact decoded degree, not merely the degree of the uncollected term list. -/
def degree {n : ℕ} (p : PolynomialCode n) : ℕ :=
  RawPolynomialCode.totalDegree (RawPolynomialCode.ofFixed p)

theorem degree_eq_totalDegree {n : ℕ} (p : PolynomialCode n) :
    degree p = (PolynomialCode.decode p).totalDegree :=
  RawPolynomialCode.totalDegree_ofFixed p

theorem ofFixed_primrec (n : ℕ) :
    Primrec (RawPolynomialCode.ofFixed : PolynomialCode n → RawPolynomialCode) := by
  apply Primrec.list_map Primrec.id
  apply Primrec.pair
  · apply Primrec.list_ofFn
    intro i
    exact Primrec.fin_app.comp (Primrec.fst.comp Primrec.snd) (Primrec.const i)
  · exact Primrec.snd.comp Primrec.snd

theorem degree_primrec (n : ℕ) : Primrec (degree : PolynomialCode n → ℕ) :=
  RawPolynomialCode.totalDegree_primrec.comp (ofFixed_primrec n)

theorem coefficientMassCode_primrec (n : ℕ) :
    Primrec (PolynomialCode.cubeAbsBoundCode : PolynomialCode n → RationalCode) :=
  PolynomialCode.cubeAbsBoundCode_primrec

theorem decode_cubeAbsBoundCode_of_decode_rename {n : ℕ} (e : σ ≃ Fin n)
    (p : MvPolynomial σ ℚ) (c : PolynomialCode n)
    (hc : PolynomialCode.decode c = MvPolynomial.rename e p) :
    RationalCode.decode (PolynomialCode.cubeAbsBoundCode c) =
      Simulation.AbsFormula.coefficientMass p := by
  rw [decode_cubeAbsBoundCode, hc, coefficientMass_rename_equiv]

theorem degree_of_decode_rename {n : ℕ} (e : σ ≃ Fin n)
    (p : MvPolynomial σ ℚ) (c : PolynomialCode n)
    (hc : PolynomialCode.decode c = MvPolynomial.rename e p) :
    degree c = p.totalDegree := by
  rw [degree_eq_totalDegree, hc, totalDegree_rename_equiv]

theorem decode_pderiv_of_decode_rename {n : ℕ} (e : σ ≃ Fin n)
    (p : MvPolynomial σ ℚ) (c : PolynomialCode n)
    (hc : PolynomialCode.decode c = MvPolynomial.rename e p) (i : σ) :
    PolynomialCode.decode (PolynomialCode.pderiv (e i) c) =
      MvPolynomial.rename e (MvPolynomial.pderiv i p) := by
  rw [PolynomialCode.decode_pderiv, hc, pderiv_rename_equiv]

end Stability.PolynomialCodeRealization
