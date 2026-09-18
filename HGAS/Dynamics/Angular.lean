import HGAS.Algebra.FiniteEuclidean
import HGAS.Propagation.DegreePadding
import Mathlib.Tactic

/-!
# Radial and angular components on a sphere

For a vector field `F` and a point `u` on the Euclidean unit sphere, write

```
a_F(u) = u · F(u),
Y_F(u) = F(u) - a_F(u)u.
```

Then `Y_F` is tangent to the sphere and `F = Y_F + a_F u`.  These are the
algebraic identities behind the angular GAS criterion and the
product-sphere wrapper.  They are kept separate from ODE and invariant
measure arguments so all later constructions can share one definition.
-/

namespace HGAS

variable {n : ℕ} {R : Type*}

/-- Radial reward of a vector field at a point.  On the unit sphere this is
the logarithmic radial velocity in angular time. -/
def radialReward [CommRing R]
    (F : FinVector n R → FinVector n R) (u : FinVector n R) : R :=
  dot u (F u)

/-- Angular component of a vector field, normalized for the unit sphere. -/
def angularField [CommRing R]
    (F : FinVector n R → FinVector n R) :
    FinVector n R → FinVector n R :=
  fun u i ↦ F u i - radialReward F u * u i

/-- Pointwise radial-angular decomposition. -/
theorem angularField_add_radial [CommRing R]
    (F : FinVector n R → FinVector n R) (u : FinVector n R) :
    angularField F u + radialReward F u • u = F u := by
  funext i
  simp [angularField, Pi.smul_apply, smul_eq_mul]

/-- Before imposing unit length, the angular component's radial dot product
is `a_F(u)(1-‖u‖²)`. -/
theorem dot_angularField [CommRing R]
    (F : FinVector n R → FinVector n R) (u : FinVector n R) :
    dot u (angularField F u) =
      radialReward F u * (1 - normSq u) := by
  simp only [dot, angularField, radialReward, normSq]
  rw [Finset.sum_congr rfl (fun i _ ↦ by
    change u i * (F u i - (∑ j, u j * F u j) * u i) =
      u i * F u i - (∑ j, u j * F u j) * (u i * u i)
    ring)]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- The angular component is tangent to the unit sphere. -/
theorem angularField_tangent [CommRing R]
    (F : FinVector n R → FinVector n R) (u : FinVector n R)
    (hu : normSq u = 1) :
    dot u (angularField F u) = 0 := by
  rw [dot_angularField, hu]
  ring

/-- A scaling-homogeneous field has radial reward of scaling degree one
higher. -/
theorem radialReward_smul [CommRing R]
    (F : FinVector n R → FinVector n R) (d : ℕ)
    (hF : ScalesAsDegree R d F) (c : R) (x : FinVector n R) :
    radialReward F (c • x) =
      c ^ (d + 1) * radialReward F x := by
  simp only [radialReward, hF c x, dot_smul_left, dot_smul_right, pow_succ]
  ring

/-- Odd-degree fields are odd maps. -/
theorem map_neg_of_scalesAsDegree_of_odd [CommRing R]
    (F : FinVector n R → FinVector n R) (d : ℕ)
    (hF : ScalesAsDegree R d F) (hd : Odd d)
    (x : FinVector n R) :
    F (-x) = -F x := by
  rw [← neg_one_smul R x, hF, hd.neg_one_pow, neg_one_smul]

/-- Even-degree fields are even maps. -/
theorem map_neg_of_scalesAsDegree_of_even [CommRing R]
    (F : FinVector n R → FinVector n R) (d : ℕ)
    (hF : ScalesAsDegree R d F) (hd : Even d)
    (x : FinVector n R) :
    F (-x) = F x := by
  rw [← neg_one_smul R x, hF, hd.neg_one_pow, one_smul]

/-- Every positive-degree homogeneous field vanishes at the origin. -/
theorem map_zero_of_scalesAsDegree [CommRing R]
    (F : FinVector n R → FinVector n R) (d : ℕ)
    (hF : ScalesAsDegree R d F) (hd : 0 < d) :
    F 0 = 0 := by
  have h := hF 0 (0 : FinVector n R)
  simpa [zero_pow hd.ne'] using h

end HGAS
