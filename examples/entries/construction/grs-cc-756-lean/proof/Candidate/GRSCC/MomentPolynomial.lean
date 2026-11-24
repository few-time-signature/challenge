import Candidate.GRSCC.SupplierFold

/-! The coefficient of X^(v+7w) in (1+aX+bX^7)^6 is
6!/(v! w! (6-v-w)!) times the supplier moment a^v b^w.
A single integer evaluation counts all the moments for one mask. -/
namespace PoissonDAG.GRSCC.MomentPolynomial
open Small SupplierFold

abbrev base : Nat := 2^200
def hist (p : Nat) := p / radix^16 % radix
def comp (free r : Nat) := factor 9^free / radix^r % radix

/-- Sum a function of the two supplier counts over all target completions. -/
def mass (f : Nat → Nat → Nat) (free : Nat) : List Action → Nat → Nat → Nat → Nat
  | [], r,p,u => comp free r * f (hist p) u
  | .skip w s :: xs, r,p,u => mass f free xs r (p*factor 9) (u+w*hist (p*s))
  | .select :: xs, r,p,u => ((List.range (min 8 r)).map (fun d =>
      mass f free xs (r-(d+1)) (p*factor (d+1)) u)).sum

def measure (mask : Nat) (f : Nat → Nat → Nat) :=
  mass f (6-(selectedPositions mask).length) (pattern mask) 16 1 0

private theorem mass_int (m v free : Nat) (xs : List Action) (r p u : Nat) :
    (mass (fun a b => a^v*b^(m-v)) free xs r p u : Int) =
      SupplierFold.sum free m v xs r p u := by
  induction xs generalizing r p u with
  | nil => simp [mass,SupplierFold.sum,total,comp,completions,hist,histogramDigit]
  | cons cmd xs ih =>
    cases cmd with
    | skip w s =>
      simpa only [mass,SupplierFold.sum,charge,hist,histogramDigit,Nat.cast_add,Nat.cast_mul] using
        ih r (p*factor 9) (u+w*hist (p*s))
    | select => simp [mass,SupplierFold.sum,List.map_map,Function.comp_def,ih]

theorem signed (m v mask : Nat) :
    SupplierFold.contribution m v mask = subsetSign mask *
      (measure mask (fun a b => a^v*b^(m-v)) : Nat) := by
  unfold contribution measure
  rw [mass_int]
  rfl

private theorem mass_linear (f g : Nat → Nat → Nat) (k free : Nat)
    (xs : List Action) (r p u : Nat) :
    mass (fun a b => f a b + k*g a b) free xs r p u =
      mass f free xs r p u + k*mass g free xs r p u := by
  induction xs generalizing r p u with
  | nil => simp [mass]; ring
  | cons cmd xs ih =>
    cases cmd with
    | skip w s => exact ih _ _ _
    | select =>
      simp only [mass,ih]
      simp [←List.sum_map_mul_left,←List.sum_map_add]

private theorem mass_zero (free : Nat) (xs : List Action) (r p u : Nat) :
    mass (fun _ _ => 0) free xs r p u = 0 := by
  induction xs generalizing r p u with
  | nil => simp [mass]
  | cons cmd xs ih => cases cmd <;> simp [mass,ih]

def horner (x : Nat) : List Nat → Nat
  | [] => 0
  | a :: as => a+x*horner x as

structure Term where
  multiplicity : Nat
  same : Nat
  different : Nat

def monomial (e : Term) (a b : Nat) := e.multiplicity * (a^e.same * b^e.different)

/-- Entry k describes the coefficient of degree k. -/
def terms : List Term :=
  [⟨1, 0, 0⟩, ⟨6, 1, 0⟩, ⟨15, 2, 0⟩, ⟨20, 3, 0⟩, ⟨15, 4, 0⟩, ⟨6, 5, 0⟩, ⟨1, 6, 0⟩,
   ⟨6, 0, 1⟩, ⟨30, 1, 1⟩, ⟨60, 2, 1⟩, ⟨60, 3, 1⟩, ⟨30, 4, 1⟩, ⟨6, 5, 1⟩, ⟨0, 6, 1⟩,
   ⟨15, 0, 2⟩, ⟨60, 1, 2⟩, ⟨90, 2, 2⟩, ⟨60, 3, 2⟩, ⟨15, 4, 2⟩, ⟨0, 5, 2⟩, ⟨0, 6, 2⟩,
   ⟨20, 0, 3⟩, ⟨60, 1, 3⟩, ⟨60, 2, 3⟩, ⟨20, 3, 3⟩, ⟨0, 4, 3⟩, ⟨0, 5, 3⟩, ⟨0, 6, 3⟩,
   ⟨15, 0, 4⟩, ⟨30, 1, 4⟩, ⟨15, 2, 4⟩, ⟨0, 3, 4⟩, ⟨0, 4, 4⟩, ⟨0, 5, 4⟩, ⟨0, 6, 4⟩,
   ⟨6, 0, 5⟩, ⟨6, 1, 5⟩, ⟨0, 2, 5⟩, ⟨0, 3, 5⟩, ⟨0, 4, 5⟩, ⟨0, 5, 5⟩, ⟨0, 6, 5⟩,
   ⟨1, 0, 6⟩]

private theorem expansion (a b x : Nat) :
    (1+a*x+b*x^7)^6 = horner x (terms.map (fun e => monomial e a b)) := by
  simp only [terms,List.map_cons,List.map_nil,horner,monomial]
  ring

private theorem integral (mask x : Nat) (es : List Term) :
    measure mask (fun a b => horner x (es.map (fun e => monomial e a b))) =
      horner x (es.map (fun e => measure mask (monomial e))) := by
  induction es with
  | nil => exact mass_zero _ _ _ _ _
  | cons e es ih =>
    simp only [List.map_cons,horner]
    unfold measure at ih ⊢
    rw [mass_linear,ih]

def packed (mask x : Nat) := measure mask (fun a b => (1+a*x+b*x^7)^6)

private theorem packed_eq (mask x : Nat) :
    packed mask x = horner x (terms.map (fun e => measure mask (monomial e))) := by
  unfold packed
  simp_rw [expansion]
  exact integral _ _ _

private def weight (xs : List Action) : Nat :=
  match xs with
  | [] => 0
  | .skip w _ :: tail => w*radix + weight tail
  | .select :: tail => weight tail

private theorem mass_bound (free : Nat) (xs : List Action) (r p u : Nat) :
    mass (fun a b => (1+a*1+b*1^7)^6) free xs r p u ≤
      8^xs.length * radix * (1+radix+u+weight xs)^6 := by
  have hd (x : Nat) : hist x ≤ radix := (Nat.mod_lt _ (by decide : 0<radix)).le
  have hc (t : Nat) : comp free t ≤ radix := (Nat.mod_lt _ (by decide : 0<radix)).le
  induction xs generalizing r p u with
  | nil =>
    simp only [mass,List.length_nil,pow_zero,one_mul,weight,Nat.add_zero,Nat.mul_one,one_pow]
    gcongr
    all_goals first | exact hc _ | exact hd _
  | cons cmd xs ih =>
    cases cmd with
    | skip w s =>
      simp only [mass,List.length_cons,weight,pow_succ (8:Nat)]
      apply (ih _ _ _).trans
      apply Nat.mul_le_mul
      · apply Nat.mul_le_mul_right
        omega
      · apply Nat.pow_le_pow_left
        have h := Nat.mul_le_mul_left w (hd (p*s))
        omega
    | select =>
      simp only [mass,List.length_cons,weight,pow_succ (8:Nat)]
      let z := 8^xs.length * radix * (1+radix+u+weight xs)^6
      have hsum (ds : List Nat) : (ds.map (fun d => mass (fun a b => (1+a*1+b*1^7)^6)
          free xs (r-(d+1)) (p*factor (d+1)) u)).sum ≤ ds.length*z := by
        induction ds with
        | nil => simp
        | cons d ds h =>
          simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul]
          exact (Nat.add_le_add (ih _ _ _) h).trans_eq (Nat.add_comm ..)
      apply (hsum _).trans
      rw [List.length_range]
      exact (Nat.mul_le_mul_right _ (Nat.min_le_left 8 r)).trans_eq (by unfold z; ring)

private theorem horner_one (xs : List Nat) : horner 1 xs = xs.sum := by
  induction xs <;> simp [horner, *]

private theorem digit (xs : List Nat) (i : Nat) (small : xs.sum < base) :
    (horner base xs / base^i) % base = xs[i]?.getD 0 := by
  induction xs generalizing i with
  | nil => simp [horner]
  | cons a xs ih =>
    simp only [List.sum_cons] at small
    have ha : a < base := by omega
    have ht : xs.sum < base := by omega
    cases i with
    | zero => simp [horner,Nat.mod_eq_of_lt ha]
    | succ i =>
      rw [horner,pow_succ',←Nat.div_div_eq_div_mul,
        Nat.add_mul_div_left _ _ (by decide : 0<base),Nat.div_eq_of_lt ha,Nat.zero_add]
      exact ih i ht

private theorem bound63 : ∀ mask : Fin 63,
    8^(pattern mask).length * radix * (1+radix+0+weight (pattern mask))^6 < base := by
  decide +kernel

theorem extract (mask : Fin 63) (i : Nat) :
    (packed mask base / base^i) % base =
      ((terms.map (fun e => measure mask (monomial e)))[i]?).getD 0 := by
  rw [packed_eq]
  apply digit
  rw [←horner_one,←packed_eq]
  exact (mass_bound _ _ _ _ _).trans_lt (bound63 mask)

theorem monomial_mass (mask : Nat) (e : Term) :
    measure mask (monomial e) = e.multiplicity * measure mask (fun a b => a^e.same*b^e.different) := by
  unfold measure monomial
  simpa [mass_zero] using mass_linear (fun _ _ => 0) (fun a b => a^e.same*b^e.different)
    e.multiplicity (6-(selectedPositions mask).length) (pattern mask) 16 1 0

end PoissonDAG.GRSCC.MomentPolynomial
