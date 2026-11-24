import Candidate.Constructions.PORS.ChainLeafMarks
import Candidate.Constructions.PORS.BucketCoordGates

namespace PoissonDAG.PORS.ChainCoord

open RankGates Literal LiteralMaskSemantics ChainLeafGates PrunedCount

def inner (cap : Nat) (xs : List (Nat×Nat)) (s : Shape) (off : Nat) : View :=
  shapeView true (fun i => chainView cap i xs) s off

private theorem active_count (cap : Nat) (xs : List (Nat×Nat)) (s : Shape) (off : Nat) :
    let v := shapeView true (fun i => leafView (live xs i)) s off
    (inner cap xs s off).active=v.active ∧ (inner cap xs s off).count=v.count := by
  induction s generalizing off with
  | leaf => exact ⟨rfl,rfl⟩
  | branch l r il ir =>
    obtain ⟨al,cl⟩ := il off
    obtain ⟨ar,cr⟩ := ir (off+l.leaves)
    change (joinView true (inner cap xs l off) (inner cap xs r (off+l.leaves))).active=_ ∧
      (joinView true (inner cap xs l off) (inner cap xs r (off+l.leaves))).count=_
    simp only [shapeView,joinView,al,cl,ar,cr,and_self]

theorem inner_count_le (cap : Nat) (xs : List (Nat×Nat)) (s : Shape) (off : Nat) :
    (inner cap xs s off).count+1 ≤ s.leaves := by
  rw [(active_count cap xs s off).2]
  exact child_count_le s (live xs) off

theorem inner_support (cap : Nat) (xs : List (Nat×Nat)) (s : Shape) (off : Nat)
    (u : Finset (Leaf s)) (agree : ∀ x, live xs (off+(leafIndex s x).val)=true ↔ x∈u) :
    (inner cap xs s off).active=decide (0<u.card) ∧ (inner cap xs s off).count=siblings s u := by
  have h := active_count cap xs s off
  have g := child_support s off (live xs) u agree
  exact ⟨h.1.trans g.1,h.2.trans g.2⟩

private theorem inner_fits (cap : Nat) (xs : List (Nat×Nat)) (w : Nat)
    (s : Shape) (off : Nat) (room : s.leaves ≤ 2^w) :
    Fits true (fun i => chainView cap i xs) w s off := by
  induction s generalizing off with
  | leaf => trivial
  | branch l r il ir =>
    change l.leaves+r.leaves ≤ 2^w at room
    refine ⟨?_,il off (by omega),ir (off+l.leaves) (by omega)⟩
    change (inner cap xs (.branch l r) off).count < 2^w
    rw [(active_count cap xs (.branch l r) off).2]
    have h := child_count_le (.branch l r) (live xs) off
    change _ + 1 ≤ l.leaves+r.leaves at h
    omega

theorem atCoord_chain (row : Row) (child outer : Shape) {raw p} (seed : Seeded raw p)
    (d : Digits) (xs : List (Nat×Nat)) (idx : Nat)
    (digits : paired raw p (width row) (d.leaves.zip d.depths) xs)
    (bucket : Number raw p (width row) d.bucket idx) (hchild : child.leaves ≤ 2^(width row))
    (houter : outer.leaves ≤ 2^(width row)) (hw : 0<width row) (hc : row.cap < 2^(width row)) :
    Builds raw p (atCoord row child outer d) (fun q a => Represents raw q (width row) a
      (BucketCoord.coordView outer (inner row.cap xs child 0) idx)) := by
  apply BucketCoord.atCoord_of_inner row child outer seed d idx _ bucket houter hw
  apply atShape_spec _ _ _ _ _ _ _ _ seed hw
  · intro i _ hi q e
    exact atLeaf_chain row (seed.mono e) d xs (paired_mono digits e) i (by omega) hc
  · exact inner_fits _ _ _ _ _ hchild

open ChainRefined in
theorem production_coord {raw g} (seed : Seeded raw g) (d : Digits) (xs : List (Nat×Nat)) (idx : Nat)
    (digits : paired raw g (width p) (d.leaves.zip d.depths) xs)
    (bucket : Number raw g (width p) d.bucket idx) :
    Builds raw g (atCoord p (shape p.t) (shape p.buckets) d) (fun q out =>
      Represents raw q (width p) out (BucketCoord.coordView (shape p.buckets)
        (inner p.cap xs (shape p.t) 0) idx)) := by
  apply atCoord_chain p _ _ seed d xs idx digits bucket
  · rw [shape_card _ (by decide +kernel)]; decide +kernel
  · rw [shape_card _ (by decide +kernel)]; decide +kernel
  · decide +kernel
  · decide +kernel

end PoissonDAG.PORS.ChainCoord
