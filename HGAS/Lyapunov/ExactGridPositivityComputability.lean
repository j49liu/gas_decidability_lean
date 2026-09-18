import HGAS.Lyapunov.ExactGridPositivity
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.RE

/-!
# Computability of exact finite-grid positivity certificates

`ExactGridPositivity` gives the semantic correctness and completeness of
the finite rational grid test.  This companion file verifies that its
arithmetic and finite-list components are primitive recursive.  Keeping
these declarations separate makes the geometric proof independent of the
particular computability library API.
-/

namespace HGAS

namespace RationalCode

theorem abs_primrec : Primrec abs :=
  Primrec.pair
    (Primrec.pair (Primrec.const false)
      (Primrec.snd.comp Primrec.fst))
    Primrec.snd

theorem sub_primrec : Primrec₂ sub :=
  RationalCode.add_primrec.comp
    Primrec.fst
    (RationalCode.neg_primrec.comp Primrec.snd)

theorem pow_primrec : Primrec₂ pow := by
  have hstep :
      Primrec₂
        (fun q : RationalCode =>
          fun state : ℕ × RationalCode =>
            RationalCode.mul q state.2) :=
    RationalCode.mul_primrec.comp₂
      Primrec₂.left
      (Primrec.snd.comp₂ Primrec₂.right)
  exact
    (Primrec.nat_rec (Primrec.const RationalCode.one) hstep).of_eq
      fun q k ↦ by
        induction k with
        | zero => rfl
        | succ k ih =>
            change
              RationalCode.mul q
                  (Nat.rec RationalCode.one
                    (fun _ r ↦ RationalCode.mul q r) k) =
                RationalCode.mul q (RationalCode.pow q k)
            rw [ih]

theorem unitFraction_primrec : Primrec unitFraction :=
  Primrec.pair
    (Primrec.const (false, 1))
    (Primrec.nat_sub.comp Primrec.id (Primrec.const 1))

theorem lt_primrec : Primrec₂ lt :=
  RationalCode.positive_primrec.comp
    (RationalCode.sub_primrec.comp
      Primrec.snd Primrec.fst)

end RationalCode

namespace PolynomialCode

variable {n : ℕ}

private theorem list_dedup_primrec
    {α : Type*} [Primcodable α] [DecidableEq α] :
    Primrec (@List.dedup α _) := by
  have hmem :
      PrimrecPred
        (fun q : α × List α ↦ q.1 ∈ q.2) := by
    exact
      ((PrimrecRel.exists_mem_list
        (Primrec.eq : PrimrecRel (@Eq α))).comp
          Primrec.snd Primrec.fst).of_eq fun q ↦ by simp
  have hstep :
      Primrec₂
        (fun (_ : List α)
          (state : α × List α × List α) ↦
          if state.1 ∈ state.2.1 then state.2.2
          else state.1 :: state.2.2) :=
    Primrec.ite
      (hmem.comp
        (Primrec.pair
          (Primrec.fst.comp Primrec.snd)
          (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.list_cons.comp
        (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  exact
    (Primrec.list_rec Primrec.id (Primrec.const []) hstep).of_eq
      fun l ↦ by
        induction l with
        | nil => rfl
        | cons a l ih =>
            simp only [id_eq]
            rw [List.dedup_cons]
            split <;> simp_all

theorem evalMonomialCode_primrec :
    Primrec₂
      (evalMonomialCode :
        ExponentCode n → (Fin n → RationalCode) → RationalCode) := by
  have hterms :
      Primrec
        (fun q : ExponentCode n × (Fin n → RationalCode) ↦
          List.ofFn fun i : Fin n ↦
            RationalCode.pow (q.2 i) (q.1 i)) :=
    Primrec.list_ofFn fun i ↦
      RationalCode.pow_primrec.comp
        (Primrec.fin_app.comp Primrec.snd (Primrec.const i))
        (Primrec.fin_app.comp Primrec.fst (Primrec.const i))
  have hstep :
      Primrec₂
        (fun (_ : ExponentCode n × (Fin n → RationalCode))
          (state : RationalCode × RationalCode) ↦
            RationalCode.mul state.1 state.2) :=
    RationalCode.mul_primrec.comp₂
      (Primrec.fst.comp₂ Primrec₂.right)
      (Primrec.snd.comp₂ Primrec₂.right)
  exact
    (Primrec.list_foldr hterms
      (Primrec.const RationalCode.one) hstep).to₂.of_eq
      fun _ _ ↦ rfl

theorem evalCode_primrec :
    Primrec₂
      (evalCode :
        PolynomialCode n → (Fin n → RationalCode) → RationalCode) := by
  have hmonomial :
      Primrec₂
        (fun (q : PolynomialCode n × (Fin n → RationalCode))
          (state :
            (ExponentCode n × RationalCode) × RationalCode) ↦
          evalMonomialCode state.1.1 q.2) :=
    evalMonomialCode_primrec.comp₂
      (Primrec.fst.comp₂
        (Primrec.fst.comp₂ Primrec₂.right))
      (Primrec.snd.comp₂ Primrec₂.left)
  have hstep :
      Primrec₂
        (fun (q : PolynomialCode n × (Fin n → RationalCode))
          (state :
            (ExponentCode n × RationalCode) × RationalCode) ↦
          RationalCode.add
            (RationalCode.mul state.1.2
              (evalMonomialCode state.1.1 q.2))
            state.2) :=
    RationalCode.add_primrec.comp₂
      (RationalCode.mul_primrec.comp₂
        (Primrec.snd.comp₂
          (Primrec.fst.comp₂ Primrec₂.right))
        hmonomial)
      (Primrec.snd.comp₂ Primrec₂.right)
  exact
    (Primrec.list_foldr Primrec.fst
      (Primrec.const RationalCode.zero) hstep).to₂.of_eq
      fun p x ↦ by
        induction p with
        | nil => rfl
        | cons t p ih =>
            change
              RationalCode.add
                  (RationalCode.mul t.2
                    (evalMonomialCode t.1 x))
                  (List.foldr
                    (fun t r ↦
                      RationalCode.add
                        (RationalCode.mul t.2
                          (evalMonomialCode t.1 x)) r)
                    RationalCode.zero p) =
                evalCode (t :: p) x
            rw [evalCode]
            congr

theorem rawAbsBoundCode_primrec :
    Primrec (rawAbsBoundCode : PolynomialCode n → RationalCode) := by
  have hstep :
      Primrec₂
        (fun (_ : PolynomialCode n)
          (state :
            (ExponentCode n × RationalCode) × RationalCode) ↦
          RationalCode.add (RationalCode.abs state.1.2) state.2) :=
    RationalCode.add_primrec.comp₂
      (RationalCode.abs_primrec.comp₂
        (Primrec.snd.comp₂
          (Primrec.fst.comp₂ Primrec₂.right)))
      (Primrec.snd.comp₂ Primrec₂.right)
  exact
    (Primrec.list_foldr Primrec.id
      (Primrec.const RationalCode.zero) hstep).of_eq
      fun p ↦ by
        induction p with
        | nil => rfl
        | cons t p ih =>
            change
              RationalCode.add (RationalCode.abs t.2)
                  (List.foldr
                    (fun t r ↦
                      RationalCode.add
                        (RationalCode.abs t.2) r)
                    RationalCode.zero p) =
                rawAbsBoundCode (t :: p)
            rw [rawAbsBoundCode]
            apply congrArg (RationalCode.add (RationalCode.abs t.2))
            simpa only [id_eq] using ih

theorem cubeAbsBoundCode_primrec :
    Primrec (cubeAbsBoundCode : PolynomialCode n → RationalCode) := by
  have hexponents :
      Primrec
        (fun p : PolynomialCode n ↦ p.exponents.dedup) :=
    list_dedup_primrec.comp PolynomialCode.exponents_primrec
  have hcoefficient :
      Primrec₂
        (fun (p : PolynomialCode n) (e : ExponentCode n) ↦
          RationalCode.abs (p.coefficient e)) :=
    RationalCode.abs_primrec.comp₂
      (PolynomialCode.coefficient_primrec.comp₂
        Primrec₂.right Primrec₂.left)
  have hcoefficients :
      Primrec
        (fun p : PolynomialCode n ↦
          (p.exponents.dedup.map fun e ↦
            RationalCode.abs (p.coefficient e))) :=
    Primrec.list_map hexponents hcoefficient
  have hstep :
      Primrec₂
        (fun (_ : PolynomialCode n)
          (state : RationalCode × RationalCode) ↦
          RationalCode.add state.1 state.2) :=
    RationalCode.add_primrec.comp₂
      (Primrec.fst.comp₂ Primrec₂.right)
      (Primrec.snd.comp₂ Primrec₂.right)
  exact
    (Primrec.list_foldr hcoefficients
      (Primrec.const RationalCode.zero) hstep).of_eq
      fun _ ↦ rfl

theorem cubeGradientBoundCode_primrec :
    Primrec
      (cubeGradientBoundCode :
        PolynomialCode n → RationalCode) := by
  have hderivatives :
      Primrec
        (fun p : PolynomialCode n ↦
          List.ofFn fun i : Fin n ↦
            cubeAbsBoundCode (pderiv i p)) :=
    Primrec.list_ofFn fun i ↦
      cubeAbsBoundCode_primrec.comp
        (PolynomialCode.pderiv_primrec.comp
          (Primrec.const i) Primrec.id)
  have hstep :
      Primrec₂
        (fun (_ : PolynomialCode n)
          (state : RationalCode × RationalCode) ↦
          RationalCode.add state.1 state.2) :=
    RationalCode.add_primrec.comp₂
      (Primrec.fst.comp₂ Primrec₂.right)
      (Primrec.snd.comp₂ Primrec₂.right)
  exact
    (Primrec.list_foldr hderivatives
      (Primrec.const RationalCode.zero) hstep).of_eq
      fun _ ↦ rfl

end PolynomialCode

namespace ExactGridPositivity

theorem cartesianWords_primrec
    {α : Type*} [Primcodable α] (n : ℕ) :
    Primrec (fun alphabet : List α ↦ cartesianWords alphabet n) := by
  induction n with
  | zero =>
      exact (Primrec.const [[]]).of_eq fun _ ↦ rfl
  | succ n ih =>
      have hword :
          Primrec
            (fun q : List α × α ↦
              (cartesianWords q.1 n).map fun tail ↦
                q.2 :: tail) :=
        Primrec.list_map
          (ih.comp Primrec.fst)
          (Primrec.list_cons.comp₂
            (Primrec.snd.comp₂ Primrec₂.left)
            Primrec₂.right)
      exact
        (Primrec.list_flatMap Primrec.id hword.to₂).of_eq
          fun _ ↦ rfl

theorem gridIndexPoints_primrec (n : ℕ) :
    Primrec (gridIndexPoints n) := by
  have halphabet :
      Primrec
        (fun m : ℕ ↦ List.range (2 * m + 1)) :=
    Primrec.list_range.comp
      (Primrec.succ.comp
        (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id))
  exact (cartesianWords_primrec n).comp halphabet

theorem centeredNumeratorCode_primrec :
    Primrec₂ centeredNumeratorCode := by
  have hlt :
      PrimrecPred
        (fun q : ℕ × ℕ ↦ q.2 < q.1) :=
    Primrec.nat_lt.comp Primrec.snd Primrec.fst
  exact
    (Primrec.ite hlt
      (Primrec.pair (Primrec.const true)
        (Primrec.nat_sub.comp Primrec.fst Primrec.snd))
      (Primrec.pair (Primrec.const false)
        (Primrec.nat_sub.comp Primrec.snd Primrec.fst))).to₂.of_eq
      fun _ _ ↦ rfl

theorem gridCoordinateCode_primrec :
    Primrec₂ gridCoordinateCode := by
  have hmzero :
      PrimrecPred (fun q : ℕ × ℕ ↦ q.1 = 0) :=
    Primrec.eq.comp Primrec.fst (Primrec.const 0)
  have hnonzero :
      Primrec
        (fun q : ℕ × ℕ ↦
          (centeredNumeratorCode q.1 q.2, q.1 - 1)) :=
    Primrec.pair
      (centeredNumeratorCode_primrec.comp
        Primrec.fst Primrec.snd)
      (Primrec.nat_sub.comp Primrec.fst (Primrec.const 1))
  exact
    (Primrec.ite hmzero
      (Primrec.const RationalCode.zero) hnonzero).to₂.of_eq
      fun _ _ ↦ rfl

theorem gridPointCode_primrec (n : ℕ) :
    Primrec₂ (gridPointCode n) := by
  change
    Primrec
      (fun q : ℕ × List ℕ ↦ gridPointCode n q.1 q.2)
  rw [Primrec.fin_curry]
  exact gridCoordinateCode_primrec.comp₂
    (Primrec.fst.comp₂ Primrec₂.left)
    (Primrec.list_getD 0 |>.comp₂
      (Primrec.snd.comp₂ Primrec₂.left)
      (Primrec.fin_val.comp₂ Primrec₂.right))

theorem isBoundaryIndexPoint_primrec :
    Primrec₂ isBoundaryIndexPoint := by
  have hendpoint :
      Primrec₂
        (fun (m : ℕ) (k : ℕ) ↦
          (k == 0) || (k == 2 * m)) :=
    Primrec.or.comp₂
      (Primrec.beq.comp₂ Primrec₂.right
        (Primrec.const 0).to₂)
      (Primrec.beq.comp₂ Primrec₂.right
        (Primrec.nat_mul.comp₂
          (Primrec.const 2).to₂ Primrec₂.left))
  have hstep :
      Primrec₂
        (fun (q : ℕ × List ℕ) (state : ℕ × Bool) ↦
          ((state.1 == 0) || (state.1 == 2 * q.1)) ||
            state.2) :=
    Primrec.or.comp₂
      (hendpoint.comp₂
        (Primrec.fst.comp₂ Primrec₂.left)
        (Primrec.fst.comp₂ Primrec₂.right))
      (Primrec.snd.comp₂ Primrec₂.right)
  exact
    (Primrec.list_foldr Primrec.snd
      (Primrec.const false) hstep).to₂.of_eq
      fun m point ↦ by
        induction point with
        | nil => rfl
        | cons k point ih =>
            change
              (((k == 0) || (k == 2 * m)) ||
                  List.foldr
                    (fun k b ↦
                      ((k == 0) || (k == 2 * m)) || b)
                    false point) =
                isBoundaryIndexPoint m (k :: point)
            rw [isBoundaryIndexPoint]
            change
              (((k == 0) || (k == 2 * m)) ||
                  List.foldr
                    (fun k b ↦
                      ((k == 0) || (k == 2 * m)) || b)
                    false point) =
                (((k == 0) || (k == 2 * m)) ||
                  point.any fun k ↦
                    (k == 0) || (k == 2 * m))
            congr

theorem marginCode_primrec {n : ℕ} :
    Primrec₂ (marginCode : PolynomialCode n → ℕ → RationalCode) :=
  RationalCode.mul_primrec.comp
    (PolynomialCode.cubeGradientBoundCode_primrec.comp Primrec.fst)
    (RationalCode.unitFraction_primrec.comp Primrec.snd)

theorem checkGridPoint_primrec {n : ℕ} :
    Primrec₂
      (fun q : PolynomialCode n × ℕ ↦
        checkGridPoint q.1 q.2) := by
  have hboundary :
      Primrec₂
        (fun (q : PolynomialCode n × ℕ) (point : List ℕ) ↦
          isBoundaryIndexPoint q.2 point) :=
    isBoundaryIndexPoint_primrec.comp₂
      (Primrec.snd.comp₂ Primrec₂.left)
      Primrec₂.right
  have hgrid :
      Primrec₂
        (fun (q : PolynomialCode n × ℕ) (point : List ℕ) ↦
          gridPointCode n q.2 point) :=
    gridPointCode_primrec n |>.comp₂
      (Primrec.snd.comp₂ Primrec₂.left)
      Primrec₂.right
  have hevaluation :
      Primrec₂
        (fun (q : PolynomialCode n × ℕ) (point : List ℕ) ↦
          PolynomialCode.evalCode q.1
            (gridPointCode n q.2 point)) :=
    PolynomialCode.evalCode_primrec.comp₂
      (Primrec.fst.comp₂ Primrec₂.left)
      hgrid
  have hmargin :
      Primrec₂
        (fun (q : PolynomialCode n × ℕ) (_ : List ℕ) ↦
          marginCode q.1 q.2) :=
    marginCode_primrec.comp₂
      (Primrec.fst.comp₂ Primrec₂.left)
      (Primrec.snd.comp₂ Primrec₂.left)
  exact
    (Primrec.or.comp₂
      (Primrec.not.comp₂ hboundary)
      (RationalCode.lt_primrec.comp₂ hmargin hevaluation)).of_eq
      fun _ _ ↦ rfl

theorem checkStrictPositiveOnSupSphere_primrec {n : ℕ} :
    Primrec₂
      (checkStrictPositiveOnSupSphere :
        PolynomialCode n → ℕ → Bool) := by
  have hpositive :
      Primrec
        (fun q : PolynomialCode n × ℕ ↦
          decide (0 < q.2)) :=
    (Primrec.nat_lt.comp
      (Primrec.const 0) Primrec.snd).decide
  have hstep :
      Primrec₂
        (fun (q : PolynomialCode n × ℕ)
          (state : List ℕ × Bool) ↦
          checkGridPoint q.1 q.2 state.1 && state.2) :=
    Primrec.and.comp₂
      (checkGridPoint_primrec.comp₂
        Primrec₂.left
        (Primrec.fst.comp₂ Primrec₂.right))
      (Primrec.snd.comp₂ Primrec₂.right)
  have hall :
      Primrec
        (fun q : PolynomialCode n × ℕ ↦
          (gridIndexPoints n q.2).all
            (checkGridPoint q.1 q.2)) :=
    (Primrec.list_foldr
      (gridIndexPoints_primrec n |>.comp Primrec.snd)
      (Primrec.const true) hstep).of_eq
      fun q ↦ by
        induction gridIndexPoints n q.2 with
        | nil => rfl
        | cons point points ih =>
            change
              (checkGridPoint q.1 q.2 point &&
                  List.foldr
                    (fun point b ↦
                      checkGridPoint q.1 q.2 point && b)
                    true points) =
                (checkGridPoint q.1 q.2 point &&
                  points.all (checkGridPoint q.1 q.2))
            rw [ih]
  exact
    (Primrec.and.comp hpositive hall).to₂.of_eq
      fun _ _ ↦ rfl

/-! ## The recursively enumerable positivity language -/

/-- The primitive-recursive witness relation: `m` is an accepted exact
grid resolution for `p`. -/
def GridCertificateRelation {n : ℕ}
    (p : PolynomialCode n) (m : ℕ) : Prop :=
  checkStrictPositiveOnSupSphere p m = true

instance {n : ℕ} :
    DecidableRel
      (GridCertificateRelation :
        PolynomialCode n → ℕ → Prop) :=
  fun p m ↦ by
    unfold GridCertificateRelation
    infer_instance

theorem gridCertificateRelation_computable (n : ℕ) :
    ComputablePred
      (fun q : PolynomialCode n × ℕ ↦
        GridCertificateRelation q.1 q.2) := by
  refine ComputablePred.computable_iff.mpr ?_
  exact
    ⟨_, (checkStrictPositiveOnSupSphere_primrec (n := n)).to_comp,
      rfl⟩

/-- A polynomial code has a finite exact positivity certificate when some
resolution is accepted. -/
def HasGridCertificate {n : ℕ} (p : PolynomialCode n) : Prop :=
  ∃ m : ℕ, GridCertificateRelation p m

private theorem rePred_exists_nat_of_computableRel
    {α : Type*} [Primcodable α]
    (R : α → ℕ → Prop)
    (hR : ComputablePred (fun p : α × ℕ ↦ R p.1 p.2)) :
    REPred (fun a ↦ ∃ code, R a code) := by
  let pairDecision :
      DecidablePred (fun p : α × ℕ ↦ R p.1 p.2) :=
    hR.choose
  letI : DecidableRel R :=
    fun a code ↦ pairDecision (a, code)
  have hsearch :
      Partrec
        (fun a ↦ Nat.rfind
          (fun code ↦ Part.some (decide (R a code)))) :=
    Partrec.rfind hR.decide.partrec
  refine (Partrec.dom_re hsearch).of_eq ?_
  intro a
  rw [Nat.rfind_dom]
  simp

/-- For fixed dimension, existence of an exact finite-grid certificate is
recursively enumerable. -/
theorem hasGridCertificate_re (n : ℕ) :
    REPred (HasGridCertificate : PolynomialCode n → Prop) := by
  exact rePred_exists_nat_of_computableRel
    GridCertificateRelation
    (gridCertificateRelation_computable n)

/-- Consequently, strict positivity of a decoded rational polynomial on
the real sup-sphere is recursively enumerable.  Soundness and completeness
of the grid certificate are what identify this semantic language with the
computable existential witness language. -/
theorem strictlyPositiveOnSupSphere_re (n : ℕ) :
    REPred
      (fun p : PolynomialCode n ↦
        StrictlyPositiveOnSupSphere (PolynomialCode.decode p)) := by
  apply REPred.of_eq (hasGridCertificate_re n)
  intro p
  exact exists_checked_iff_strictlyPositiveOnSupSphere p

/-- One Boolean witness checker for the conjunction of degree-`d`
homogeneity and strict positivity. -/
def checkHomogeneousGridCertificate {n : ℕ}
    (d : ℕ) (p : PolynomialCode n) (m : ℕ) : Bool :=
  PolynomialCode.homogeneous d p &&
    checkStrictPositiveOnSupSphere p m

theorem checkHomogeneousGridCertificate_primrec
    {n : ℕ} (d : ℕ) :
    Primrec₂
      (checkHomogeneousGridCertificate d :
        PolynomialCode n → ℕ → Bool) :=
  Primrec.and.comp
    (PolynomialCode.homogeneous_primrec.comp
      (Primrec.const d) Primrec.fst)
    checkStrictPositiveOnSupSphere_primrec

def HomogeneousGridCertificateRelation {n : ℕ}
    (d : ℕ) (p : PolynomialCode n) (m : ℕ) : Prop :=
  checkHomogeneousGridCertificate d p m = true

instance {n : ℕ} (d : ℕ) :
    DecidableRel
      (HomogeneousGridCertificateRelation d :
        PolynomialCode n → ℕ → Prop) :=
  fun p m ↦ by
    unfold HomogeneousGridCertificateRelation
    infer_instance

theorem homogeneousGridCertificateRelation_computable
    (n d : ℕ) :
    ComputablePred
      (fun q : PolynomialCode n × ℕ ↦
        HomogeneousGridCertificateRelation d q.1 q.2) := by
  refine ComputablePred.computable_iff.mpr ?_
  exact
    ⟨_, (checkHomogeneousGridCertificate_primrec
      (n := n) d).to_comp, rfl⟩

theorem exists_homogeneousGridCertificate_iff
    {n d : ℕ} (p : PolynomialCode n) :
    (∃ m : ℕ, HomogeneousGridCertificateRelation d p m) ↔
      (PolynomialCode.decode p).IsHomogeneous d ∧
        StrictlyPositiveOnSupSphere (PolynomialCode.decode p) := by
  constructor
  · rintro ⟨m, hm⟩
    have hpair :
        PolynomialCode.homogeneous d p = true ∧
          checkStrictPositiveOnSupSphere p m = true := by
      simpa [HomogeneousGridCertificateRelation,
        checkHomogeneousGridCertificate] using hm
    exact
      ⟨(PolynomialCode.homogeneous_eq_true_iff d p).1 hpair.1,
        checkStrictPositiveOnSupSphere_sound p m hpair.2⟩
  · rintro ⟨hhomogeneous, hpositive⟩
    obtain ⟨m, hm⟩ :=
      checkStrictPositiveOnSupSphere_complete p hpositive
    have hhomogeneousCode :
        PolynomialCode.homogeneous d p = true :=
      (PolynomialCode.homogeneous_eq_true_iff d p).2
        hhomogeneous
    exact ⟨m, by
      simp [HomogeneousGridCertificateRelation,
        checkHomogeneousGridCertificate, hhomogeneousCode, hm]⟩

/-- For homogeneous forms, the same witness language is equivalent to
strict positivity at every nonzero real point. -/
theorem exists_homogeneousGridCertificate_iff_positive_nonzero
    {n d : ℕ} (p : PolynomialCode n) :
    (∃ m : ℕ, HomogeneousGridCertificateRelation d p m) ↔
      (PolynomialCode.decode p).IsHomogeneous d ∧
        ∀ x : Fin n → ℝ, x ≠ 0 →
          0 < ratMvPolynomialEval (PolynomialCode.decode p) x := by
  constructor
  · rintro ⟨m, hm⟩
    have hpair :
        PolynomialCode.homogeneous d p = true ∧
          checkStrictPositiveOnSupSphere p m = true := by
      simpa [HomogeneousGridCertificateRelation,
        checkHomogeneousGridCertificate] using hm
    have hhomogeneous :=
      (PolynomialCode.homogeneous_eq_true_iff d p).1 hpair.1
    exact
      ⟨hhomogeneous,
        checkStrictPositiveOnSupSphere_sound_nonzero
          p m hhomogeneous hpair.2⟩
  · rintro ⟨hhomogeneous, hpositive⟩
    obtain ⟨m, hm⟩ :=
      (exists_checked_iff_positive_nonzero
        p hhomogeneous).2 hpositive
    have hhomogeneousCode :
        PolynomialCode.homogeneous d p = true :=
      (PolynomialCode.homogeneous_eq_true_iff d p).2
        hhomogeneous
    exact ⟨m, by
      simp [HomogeneousGridCertificateRelation,
        checkHomogeneousGridCertificate, hhomogeneousCode, hm]⟩

/-- For fixed dimension and degree, the coded language of homogeneous
rational forms which are positive at every nonzero real point is
recursively enumerable. -/
theorem strictlyPositiveHomogeneousOffOrigin_re (n d : ℕ) :
    REPred
      (fun p : PolynomialCode n ↦
        (PolynomialCode.decode p).IsHomogeneous d ∧
          ∀ x : Fin n → ℝ, x ≠ 0 →
            0 < ratMvPolynomialEval
              (PolynomialCode.decode p) x) := by
  apply REPred.of_eq
    (rePred_exists_nat_of_computableRel
      (HomogeneousGridCertificateRelation d)
      (homogeneousGridCertificateRelation_computable n d))
  intro p
  exact
    exists_homogeneousGridCertificate_iff_positive_nonzero p

end ExactGridPositivity

end HGAS
