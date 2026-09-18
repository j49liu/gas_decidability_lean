import Mathlib.Tactic

/-!
# Algebraic controller and phase clocks

This module isolates the two planar polynomial fields used by the clock
construction.

The controller has coordinates `(r,s)` and parameter `p`:

```
ṙ = -s (p r² - 1),     ṡ = r (p r² - 1).
```

It preserves `r²+s²`.  On the unit circle it is at equilibrium exactly when
`p r² = 1`.  A locked controller then drives a second phase circle through

```
ċ = -(p r)d,           ḋ = (p r)c.
```

The first part of the file proves all identities over a commutative ring.
Division and order enter only in the later field and real corollaries.  No
claim about invariant measures or unique ergodicity is made here.
-/

namespace HGAS.Clocks.Controller

/-- The controller coordinates `(r,s)`.  The same type is used for its
velocity vector, whose fields are read as `(ṙ,ṡ)`. -/
@[ext]
structure ControllerState (R : Type*) where
  r : R
  s : R
deriving Repr

/-- The phase-clock coordinates `(c,d)`.  The same type is used for its
velocity vector, whose fields are read as `(ċ,ḋ)`. -/
@[ext]
structure PhaseState (R : Type*) where
  c : R
  d : R
deriving Repr

variable {R : Type*} [CommRing R]

/-- The zero controller vector. -/
def controllerOrigin : ControllerState R :=
  ⟨0, 0⟩

/-- The zero phase-clock vector. -/
def phaseOrigin : PhaseState R :=
  ⟨0, 0⟩

/-- Squared radius of the controller circle. -/
def controllerRadiusSq (x : ControllerState R) : R :=
  x.r ^ 2 + x.s ^ 2

/-- The scalar mismatch whose vanishing locks the controller. -/
def mismatch (p : R) (x : ControllerState R) : R :=
  p * x.r ^ 2 - 1

/-- The polynomial controller field
`(-s (p r²-1), r (p r²-1))`. -/
def controllerField (p : R) (x : ControllerState R) : ControllerState R :=
  ⟨-x.s * mismatch p x, x.r * mismatch p x⟩

/-- Algebraic dot product between a controller position and velocity. -/
def controllerDot (x v : ControllerState R) : R :=
  x.r * v.r + x.s * v.s

/-- A controller state is an equilibrium when its field vector is zero. -/
def IsControllerEquilibrium (p : R) (x : ControllerState R) : Prop :=
  controllerField p x = controllerOrigin

/-- Squared radius of the phase circle. -/
def phaseRadiusSq (z : PhaseState R) : R :=
  z.c ^ 2 + z.d ^ 2

/-- The constant-frequency phase field `(-ωd,ωc)`. -/
def phaseField (ω : R) (z : PhaseState R) : PhaseState R :=
  ⟨-ω * z.d, ω * z.c⟩

/-- Algebraic dot product between a phase position and velocity. -/
def phaseDot (z v : PhaseState R) : R :=
  z.c * v.c + z.d * v.d

/-- Frequency supplied to the phase clock by the controller. -/
def lockedFrequency (p : R) (x : ControllerState R) : R :=
  p * x.r

/-- The phase field driven by the controller frequency `p r`. -/
def lockedPhaseField
    (p : R) (x : ControllerState R) (z : PhaseState R) : PhaseState R :=
  phaseField (lockedFrequency p x) z

@[simp]
theorem controllerField_r (p : R) (x : ControllerState R) :
    (controllerField p x).r = -x.s * mismatch p x :=
  rfl

@[simp]
theorem controllerField_s (p : R) (x : ControllerState R) :
    (controllerField p x).s = x.r * mismatch p x :=
  rfl

/-- The controller field is tangent to every circle centered at the origin. -/
theorem controllerField_tangent (p : R) (x : ControllerState R) :
    controllerDot x (controllerField p x) = 0 := by
  simp only [controllerDot, controllerField_r, controllerField_s]
  ring

/-- Equivalently, the formal derivative of `r²+s²` along the controller
field vanishes. -/
theorem controllerRadiusSq_derivative (p : R) (x : ControllerState R) :
    2 * x.r * (controllerField p x).r +
        2 * x.s * (controllerField p x).s = 0 := by
  simp only [controllerField_r, controllerField_s]
  ring

/-- On the unit circle, the controller is at equilibrium exactly when the
locking equation `p r² = 1` holds.

This statement is slightly stronger than the form needed in the paper:
the equivalence itself does not require a prior assumption `p ≠ 0`.
Over a field, `p ≠ 0` follows automatically from the locking equation. -/
theorem isControllerEquilibrium_iff_lock_of_unit
    (p : R) (x : ControllerState R)
    (hunit : controllerRadiusSq x = 1) :
    IsControllerEquilibrium p x ↔ p * x.r ^ 2 = 1 := by
  have hunit' : x.r ^ 2 + x.s ^ 2 = 1 := by
    simpa only [controllerRadiusSq] using hunit
  constructor
  · intro hequilibrium
    have hfield : controllerField p x = controllerOrigin :=
      hequilibrium
    have hrdot : -x.s * mismatch p x = 0 := by
      simpa only [controllerField_r, controllerOrigin] using
        congrArg ControllerState.r hfield
    have hsdot : x.r * mismatch p x = 0 := by
      simpa only [controllerField_s, controllerOrigin] using
        congrArg ControllerState.s hfield
    have hsfactor : x.s * mismatch p x = 0 := by
      calc
        x.s * mismatch p x = -(-x.s * mismatch p x) := by ring
        _ = 0 := by rw [hrdot]; simp
    have hmismatch : mismatch p x = 0 := by
      calc
        mismatch p x =
            (x.r ^ 2 + x.s ^ 2) * mismatch p x := by
              rw [hunit']
              ring
        _ = x.r * (x.r * mismatch p x) +
              x.s * (x.s * mismatch p x) := by ring
        _ = 0 := by rw [hsdot, hsfactor]; ring
    exact sub_eq_zero.mp (by simpa only [mismatch] using hmismatch)
  · intro hlock
    have hmismatch : mismatch p x = 0 := by
      simpa only [mismatch] using sub_eq_zero.mpr hlock
    exact ControllerState.ext
      (by simp [controllerField, controllerOrigin, hmismatch])
      (by simp [controllerField, controllerOrigin, hmismatch])

/-- Coordinate form of the preceding equilibrium characterization. -/
theorem controllerField_eq_origin_iff_lock_of_unit
    (p : R) (x : ControllerState R)
    (hunit : controllerRadiusSq x = 1) :
    controllerField p x = controllerOrigin ↔ p * x.r ^ 2 = 1 :=
  isControllerEquilibrium_iff_lock_of_unit p x hunit

@[simp]
theorem phaseField_c (ω : R) (z : PhaseState R) :
    (phaseField ω z).c = -ω * z.d :=
  rfl

@[simp]
theorem phaseField_d (ω : R) (z : PhaseState R) :
    (phaseField ω z).d = ω * z.c :=
  rfl

/-- Every constant-frequency phase field is tangent to its phase circle. -/
theorem phaseField_tangent (ω : R) (z : PhaseState R) :
    phaseDot z (phaseField ω z) = 0 := by
  simp only [phaseDot, phaseField_c, phaseField_d]
  ring

/-- The formal derivative of `c²+d²` along a phase field vanishes. -/
theorem phaseRadiusSq_derivative (ω : R) (z : PhaseState R) :
    2 * z.c * (phaseField ω z).c +
        2 * z.d * (phaseField ω z).d = 0 := by
  simp only [phaseField_c, phaseField_d]
  ring

/-- The controller-driven phase field is tangent to the phase circle. -/
theorem lockedPhaseField_tangent
    (p : R) (x : ControllerState R) (z : PhaseState R) :
    phaseDot z (lockedPhaseField p x z) = 0 := by
  exact phaseField_tangent (lockedFrequency p x) z

/-- At a locked controller state, the square of the signed phase frequency
is exactly `p`: `(p r)² = p`. -/
theorem lockedFrequency_sq_of_lock
    (p : R) (x : ControllerState R) (hlock : p * x.r ^ 2 = 1) :
    lockedFrequency p x ^ 2 = p := by
  simp only [lockedFrequency]
  calc
    (p * x.r) ^ 2 = p * (p * x.r ^ 2) := by ring
    _ = p * 1 := by rw [hlock]
    _ = p := mul_one p

section FieldConsequences

variable {K : Type*} [Field K]

/-- The locking equation forces the controller parameter to be nonzero. -/
theorem parameter_ne_zero_of_lock
    (p : K) (x : ControllerState K) (hlock : p * x.r ^ 2 = 1) :
    p ≠ 0 := by
  intro hp
  simp [hp] at hlock

/-- For `p ≠ 0`, locking gives the exact coordinate identity `r²=1/p`. -/
theorem r_sq_eq_one_div_of_lock
    (p : K) (x : ControllerState K) (hp : p ≠ 0)
    (hlock : p * x.r ^ 2 = 1) :
    x.r ^ 2 = 1 / p := by
  apply (eq_div_iff hp).2
  simpa only [mul_comm] using hlock

/-- On the unit circle, the other locked coordinate satisfies
`s²=1-1/p`. -/
theorem s_sq_eq_one_sub_one_div_of_unit_lock
    (p : K) (x : ControllerState K) (hp : p ≠ 0)
    (hunit : controllerRadiusSq x = 1)
    (hlock : p * x.r ^ 2 = 1) :
    x.s ^ 2 = 1 - 1 / p := by
  have hunit' : x.r ^ 2 + x.s ^ 2 = 1 := by
    simpa only [controllerRadiusSq] using hunit
  calc
    x.s ^ 2 = 1 - x.r ^ 2 := by linear_combination hunit'
    _ = 1 - 1 / p := by rw [r_sq_eq_one_div_of_lock p x hp hlock]

/-- Bundled coordinate consequences for a nonzero locked parameter. -/
theorem locked_coordinate_squares
    (p : K) (x : ControllerState K) (hp : p ≠ 0)
    (hunit : controllerRadiusSq x = 1)
    (hlock : p * x.r ^ 2 = 1) :
    x.r ^ 2 = 1 / p ∧ x.s ^ 2 = 1 - 1 / p :=
  ⟨r_sq_eq_one_div_of_lock p x hp hlock,
    s_sq_eq_one_sub_one_div_of_unit_lock p x hp hunit hlock⟩

end FieldConsequences

section RealConsequences

/-- A real locking equation forces the parameter to be strictly positive. -/
theorem parameter_pos_of_lock
    (p : ℝ) (x : ControllerState ℝ) (hlock : p * x.r ^ 2 = 1) :
    0 < p := by
  have hproduct : 0 < p * x.r ^ 2 := by
    rw [hlock]
    norm_num
  exact pos_of_mul_pos_left hproduct (sq_nonneg x.r)

/-- A real locked controller on the unit circle necessarily has `p ≥ 1`. -/
theorem one_le_parameter_of_unit_lock
    (p : ℝ) (x : ControllerState ℝ)
    (hunit : controllerRadiusSq x = 1)
    (hlock : p * x.r ^ 2 = 1) :
    1 ≤ p := by
  have hunit' : x.r ^ 2 + x.s ^ 2 = 1 := by
    simpa only [controllerRadiusSq] using hunit
  have hrle : x.r ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg x.s]
  have hp : 0 ≤ p := (parameter_pos_of_lock p x hlock).le
  calc
    1 = p * x.r ^ 2 := hlock.symm
    _ ≤ p * 1 := mul_le_mul_of_nonneg_left hrle hp
    _ = p := mul_one p

end RealConsequences

end HGAS.Clocks.Controller
