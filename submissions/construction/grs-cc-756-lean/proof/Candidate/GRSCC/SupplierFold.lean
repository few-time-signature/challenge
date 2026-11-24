import Candidate.GRSCC.PrefixProducts

namespace PoissonDAG.GRSCC.SupplierFold
open Small PrunedDigits

/-- Each coordinate either requests a positive target digit, or stays free.
A free coordinate contributes the avoidance count of its preceding prefix. -/
inductive Action where
  | select
  | skip (multiplicity scale : Nat)
  deriving DecidableEq

def action (mask : Nat) (i : CodePosition) :=
  if mask.testBit i.val then Action.select
  else .skip (if i.val<5 then 2^(4-i.val) else 0) (factor 9^(6-i.val))

def pattern (mask : Nat) := (List.finRange 6).map (action mask)

def selected : List Action → Nat
  | [] => 0
  | .select :: tail => selected tail + 1
  | .skip _ _ :: tail => selected tail

def digits : List (Action × Nat) → List Nat
  | [] => []
  | (.select,d) :: xs => d :: digits xs
  | (.skip _ _,_) :: xs => digits xs

def charge : Action → Nat → Int
  | .select, _ => 0
  | .skip w s, p => w * histogramDigit (p*s)

def full : List (Action × Nat) → Nat → Int → Int × Int
  | [], p, u => (histogramDigit p,u)
  | (cmd,d) :: tail, p, u => full tail (p*factor d) (u + charge cmd p)

def eval : List Action → List Nat → Nat → Int → Int × Int
  | [], _, p, u => (histogramDigit p,u)
  | .skip w s :: tail, ds, p, u => eval tail ds (p*factor 9) (u+charge (.skip w s) p)
  | .select :: tail, d::ds, p, u => eval tail ds (p*factor d) u
  | .select :: _, [], _, _ => (0,0)

private theorem expand (xs : List (Action × Nat))
    (valid : ∀ w s d, (.skip w s,d) ∈ xs → d=9) (p u) :
    eval (xs.map Prod.fst) (digits xs) p u = full xs p u := by
  induction xs generalizing p u with
  | nil => rfl
  | cons head rest ih =>
    obtain ⟨cmd,d⟩ := head
    have hr : ∀ w s z, (.skip w s,z)∈rest → z=9 := fun w s z h => valid w s z (List.mem_cons_of_mem _ h)
    cases cmd with
    | select => simp only [List.map_cons,digits,eval,full,charge,add_zero]; exact ih hr _ _
    | skip w s =>
      have dh := valid w s d List.mem_cons_self
      subst d
      exact ih hr _ _

private def rows (mask : Nat) (b : CodePosition → Nat) (js : List CodePosition) :=
  js.map (fun j => (action mask j,b j))

private theorem select_digits (mask : Nat) (b : CodePosition → Nat) (js : List CodePosition) :
    digits (rows mask b js) = (js.filter (fun j => mask.testBit j.val)).map b := by
  induction js with
  | nil => rfl
  | cons j js ih =>
    cases h : mask.testBit j.val <;> simp [rows,action,h,digits,rows] at ih ⊢ <;> exact ih

private theorem count_selected (mask : Nat) (js : List CodePosition) :
    selected (js.map (action mask)) = (js.filter (fun j => mask.testBit j.val)).length := by
  induction js with
  | nil => rfl
  | cons j js ih => cases h : mask.testBit j.val <;> simp [action,h,selected,ih] at *

private theorem charge_at (mask : Nat) (j : CodePosition) (p : Nat) :
    charge (action mask j) p = if mask.testBit j.val then 0 else
      (if j.val<5 then 2^(4-j.val) else 0 : Nat) *
        histogramDigit (p * factor 9 ^ (6-j.val)) := by
  cases h : mask.testBit j.val <;> simp [action,charge,h]

private theorem eval_assigned (mask : Nat) (a : requirementsOfMask mask → Fin 8) :
    eval (pattern mask) (assignmentDigits mask a) 1 0 =
      supplierCounts mask (assignmentBound (requirementsOfMask mask) a) := by
  let b := assignmentBound (requirementsOfMask mask) a
  let xs := rows mask b (List.finRange 6)
  have ok : ∀ w s d, (Action.skip w s,d)∈xs → d=9 := by
    intro w s d hd
    obtain ⟨j,_,eq⟩ := List.mem_map.mp hd
    have c := congrArg Prod.fst eq
    have val := congrArg Prod.snd eq
    change action mask j = .skip w s at c
    change b j=d at val
    cases h : mask.testBit j.val
    · rw [←val]; simp [b,assignmentBound,requirementsOfMask,h]
    · simp [action,h] at c
  have marks : digits xs=assignmentDigits mask a := select_digits mask b _
  have prog : xs.map Prod.fst=pattern mask := by simp [xs,rows,pattern,List.map_map,Function.comp_def]
  rw [←marks,←prog,expand xs ok]
  change full (rows mask b (List.finRange 6)) 1 0 = supplierCounts mask b
  have all : List.finRange 6 = ([0,1,2,3,4,5] : List CodePosition) := by decide
  rw [all]
  simp only [rows,List.map_cons,List.map_nil,full,charge_at,supplierCounts]
  simp [Nat.mul_assoc,Int.add_assoc]

/-- A base-2^20 digit of a power counts the unconstrained completions.
The table has only seven possible powers and seventeen possible degrees. -/
def completions (free budget : Nat) : Int :=
  ((factor 9^free / radix^budget % radix : Nat) : Int)

private theorem completes : ∀ f : Fin 7, ∀ t : Fin 17,
    completions f t = completionFormula f t := by decide +kernel

def total (free m v budget : Nat) (x : Int × Int) :=
  completions free budget * (x.1^v * x.2^(m-v))

/-- Traverse digit choices in increasing coordinate order. The integer p
encodes the prefix histogram and u counts the other slots avoiding it. -/
def sum (free m v : Nat) : List Action → Nat → Nat → Int → Int
  | [], r, p, u => total free m v r (histogramDigit p,u)
  | .skip w s::xs, r, p, u => sum free m v xs r (p*factor 9) (u+charge (.skip w s) p)
  | .select::xs, r, p, u => ((List.range (min 8 r)).map (fun d =>
      sum free m v xs (r-(d+1)) (p*factor (d+1)) u)).sum

private theorem sum_eq (free m v : Nat) (xs : List Action) (r p u) :
    sum free m v xs r p u = fold (selected xs) r (fun ds =>
      total free m v (r-ds.sum) (eval xs ds p u)) := by
  induction xs generalizing r p u with
  | nil => simp [sum,selected,fold,eval]
  | cons op xs ih =>
    cases op with
    | skip w s => exact ih _ _ _
    | select =>
      simp only [sum,selected,fold]
      apply congrArg List.sum; apply List.map_congr_left; intro d _
      rw [ih]
      apply congrArg (fold (selected xs) (r-(d+1)))
      funext ds
      simp only [List.sum_cons,eval,Nat.sub_sub]

def contribution (m v mask : Nat) :=
  subsetSign mask * sum (6-(selectedPositions mask).length) m v (pattern mask) 16 1 0

theorem contribution_eq (m v mask : Nat) :
    contribution m v mask = directMask m v mask := by
  unfold contribution directMask
  have length_eq : selected (pattern mask) = (selectedPositions mask).length :=
    count_selected mask (List.finRange 6)
  rw [sum_eq,length_eq]
  change subsetSign mask * fold (selectedPositions mask).length 16 _ = fold _ 16 _
  rw [fold_eq_assignments,fold_eq_assignments,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro a _
  split
  next h =>
    unfold directLeaf total
    dsimp only
    rw [eval_assigned,listBound_assignmentDigits]
    have sm : ∀ j,assignmentBound (requirementsOfMask mask) a j ≤ 9 := by
      intro j; unfold assignmentBound; split
      next hj => have := (a ⟨j,hj⟩).isLt; omega
      next => decide
    rw [if_pos (decide_eq_true sm)]
    have comp := completes ⟨6-(selectedPositions mask).length,by omega⟩
      ⟨16-(assignmentDigits mask a).sum,by omega⟩
    dsimp only at comp
    rw [comp]
    split <;> simp_all [mul_left_comm,mul_comm,mul_assoc]
  next => simp

theorem bound (m v cap : Nat) (hv : 0<v) (hvm : v≤m)
    (check : ((List.range 63).map (contribution m v)).sum*1000000 ≤
      (cap : Int)*(15597^(m+1)*31^(m-v) : Nat)) : localCover m v ≤ (cap : Rat)/1000000 := by
  apply direct_of_sum _ _ _ hv hvm
  have eqn : contribution m v = directMask m v := funext (contribution_eq m v)
  rwa [←eqn]

end PoissonDAG.GRSCC.SupplierFold
