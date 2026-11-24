import Candidate.Constructions.PORS.SingleOutput
import Candidate.Constructions.PORS.SingleAccepted

namespace PoissonDAG.PORS.SingleCertificate
open Literal LiteralMaskSemantics SingleProgram SingleRefined PrunedCount

/-- Keep the tree symbolic while transporting its colex supports. This avoids
elaborating a type for each individual leaf of the production tree. -/
def readHit (t k dom raw i : Nat) : Bool :=
  decide (i ∈ (Colex.digits t k (raw%dom)).reverse)

private def readView (s : Shape) (f : Nat → Bool) :=
  shapeView true (fun i => leafView (f i)) s 0

private def readMarks (v : View) := v.prefixMarks ++ [v.root]

private abbrev U (s : Shape) (k raw : Nat) := SingleAccepted.leafSupport s k raw

private theorem decode_agrees (s : Shape) (t k dom raw : Nat) (card : s.leaves=t)
    (valid : raw<dom) (x : Leaf s) :
    readHit t k dom raw ((leafIndex s x).val) = true ↔ x ∈ U s k raw := by
  simp only [readHit,Nat.mod_eq_of_lt valid,decide_eq_true_eq,List.mem_reverse,U,
    SingleAccepted.leafSupport,Finset.mem_filter,Finset.mem_univ,true_and,
    Colex.support,List.mem_toFinset,card]
  rfl

private theorem support_size (s : Shape) (k raw : Nat) (valid : raw<s.leaves.choose k) :
    (U s k raw).card=k := by
  have hc := (Finset.mem_powersetCard.mp (Colex.support_mem valid)).2
  rwa [← SingleAccepted.address_image s k raw valid,Finset.card_map] at hc

structure RouteFacts (s : Shape) (sc : Scheme) (t k dom M bits : Nat) : Prop where
  gate : ∀ raw < 2^bits, sc.accept raw = true ↔
    raw < s.leaves.choose k ∧ siblings s (SingleAccepted.leafSupport s k raw) ≤ M
  info : ∀ raw ∈ sc.accepted, raw<dom ∧ siblings s (SingleAccepted.leafSupport s k raw) ≤ M
  agrees : ∀ raw ∈ sc.accepted, ∀ x : Leaf s,
    readHit t k dom raw (leafIndex s x).val = true ↔ x ∈ SingleAccepted.leafSupport s k raw
  weight : ∀ raw ∈ sc.accepted, (SingleAccepted.leafSupport s k raw).card=k
  route : ∀ raw ∈ sc.accepted, ∃ a : Opening (s.fill (chain 1)),
    routedOpening .leaf .leaf s 0 (fun _ => 0) (asDepth (readHit t k dom raw)) = some a ∧
    sc.frontier raw = a.marks.map Prod.fst ∧ sc.plan raw = a.marks.map Prod.snd

private theorem routeFacts (s : Shape) (sc : Scheme) (t k dom M bits : Nat) (hk : 0<k)
    (card : s.leaves=t) (cap : s.leaves.choose k=dom) (width : sc.encoder.inputs=bits)
    (fields : ∀ raw < 2^bits, let v := readView s (readHit t k dom raw)
      sc.accept raw = decide (raw<dom ∧ v.count≤M) ∧
      sc.frontier raw = (readMarks v).map Prod.fst ∧ sc.plan raw = (readMarks v).map Prod.snd) :
    RouteFacts s sc t k dom M bits := by
  have agree := decode_agrees s t k dom
  have gate (raw : Nat) (hr : raw<2^bits) : sc.accept raw = true ↔
      raw<s.leaves.choose k ∧ siblings s (U s k raw)≤M := by
    rw [(fields raw hr).1,decide_eq_true_eq,cap]
    by_cases hd : raw<dom
    · have hv := (child_support s 0 (readHit t k dom raw) (U s k raw)
          (by simpa only [Nat.zero_add] using agree raw card hd)).2
      change _ ↔ _
      rw [show (readView s (readHit t k dom raw)).count = _ from hv]
    · simp [hd]
  have info {raw : Nat} (h : raw ∈ sc.accepted) : raw < 2^bits ∧
      raw < s.leaves.choose k ∧ siblings s (U s k raw) ≤ M := by
    obtain ⟨mem,ha⟩ := List.mem_filter.mp h
    have hr : raw<2^sc.encoder.inputs := List.mem_range.mp mem
    rw [width] at hr
    exact ⟨hr,(gate raw hr).mp ha⟩
  refine ⟨gate,fun raw hm => ⟨cap ▸ (info hm).2.1,(info hm).2.2⟩,
    fun raw hm => agree raw card (cap ▸ (info hm).2.1),
    fun raw hm => support_size s k raw (info hm).2.1,?_⟩
  intro raw hm
  obtain ⟨hr,hd,_⟩ := info hm
  obtain ⟨a,ha,hmarks⟩ := route_of_nonempty s (readHit t k dom raw) (U s k raw)
    (agree raw card (cap ▸ hd)) ((support_size s k raw hd).symm ▸ hk)
  have masks := (fields raw hr).2
  exact ⟨a,ha,masks.1.trans (congrArg (List.map Prod.fst) hmarks),
    masks.2.trans (congrArg (List.map Prod.snd) hmarks)⟩

private theorem choose_eq (row : Row) (ht : 0<row.t) :
    (shape row.t).leaves.choose row.k = row.supports := by
  rw [shape_card _ ht,Nat.choose_eq_fast_choose]; rfl

private def readFields (row : Row) : Prop :=
  ∀ raw < 2^row.r, let v := readView (shape row.t) (readHit row.t row.k row.supports raw)
    (scheme row).accept raw = decide (raw<row.supports ∧ v.count≤row.M) ∧
    (scheme row).frontier raw = (readMarks v).map Prod.fst ∧
    (scheme row).plan raw = (readMarks v).map Prod.snd

private theorem row_facts (row : Row) (hk : 0<row.k) (ht : 0<row.t) (input : readFields row) :
    RouteFacts (shape row.t) (scheme row) row.t row.k row.supports row.M row.r :=
  routeFacts (shape row.t) (scheme row) row.t row.k row.supports row.M row.r hk
    (shape_card _ ht) (choose_eq row ht) (literal_inputs row) input

attribute [local irreducible] Literal.scheme Literal.shape

private theorem row_output : readFields p := by
  intro raw hr
  exact fields raw hr

theorem facts : RouteFacts child single p.t p.k p.supports p.M p.r :=
  row_facts p (by decide) (by decide) row_output

theorem count : single.accepted.length = p.acceptedWords := SingleAccepted.single_count facts.gate

end PoissonDAG.PORS.SingleCertificate
