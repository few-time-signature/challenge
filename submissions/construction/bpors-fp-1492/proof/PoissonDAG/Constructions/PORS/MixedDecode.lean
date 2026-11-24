import PoissonDAG.Constructions.PORS.RawInput
import PoissonDAG.Constructions.PORS.DepthGapWords
import PoissonDAG.Constructions.PORS.LiteralMaskLeaf

namespace PoissonDAG.PORS.RankGates.MixedDecode

structure Coordinate where
  bucket : Nat
  leaves : List Nat
  depths : List Nat

def radix (row : Row) := row.depthCount * row.supports * row.buckets

def coordinate (row : Row) (depths : Nat → List Nat) (x : Nat) : Coordinate :=
  let afterDepth := x / row.depthCount
  let afterSupport := afterDepth / row.supports
  ⟨afterSupport % row.buckets,
   (Colex.digits row.t row.k (afterDepth % row.supports)).reverse,
   depths (x % row.depthCount)⟩

theorem coordinate_mod (row : Row) (depths : Nat → List Nat) (x : Nat) :
    coordinate row depths (x % radix row) = coordinate row depths x := by
  simp only [coordinate, radix, Nat.mul_assoc, Nat.mod_mul_right_div_self,
    Nat.mod_mul_right_mod, Nat.mod_mod]

/-- Coordinates are returned least-significant first. -/
def coordinates (row : Row) (depths : Nat → List Nat) : Nat → Nat → List Coordinate
  | 0, _ => []
  | n+1, x => coordinate row depths x :: coordinates row depths n (x / radix row)

@[simp] theorem coordinates_length (row : Row) (depths : Nat → List Nat) (n x : Nat) :
    (coordinates row depths n x).length = n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp [coordinates, ih]

theorem coordinates_get (row : Row) (depths : Nat → List Nat) (n x i : Nat) (hi : i < n) :
    (coordinates row depths n x)[i]? = some (coordinate row depths (x / (radix row)^i)) := by
  induction n generalizing x i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => simp [coordinates]
    | succ i =>
      have he : radix row * (radix row)^i = (radix row)^(i+1) := by rw [Nat.pow_succ, Nat.mul_comm]
      simpa only [coordinates, List.getElem?_cons_succ, Nat.div_div_eq_div_mul, he] using
        ih (x / radix row) i (by omega)

structure Represents (raw : Nat) (p : Array Gate) (w : Nat) (d : Digits) (c : Coordinate) : Prop where
  bucket : Holds raw p w d.bucket c.bucket
  leaves : List.Forall₂ (Holds raw p w) d.leaves c.leaves
  depths : List.Forall₂ (Holds raw p w) d.depths c.depths

theorem Represents.mono {raw p q w d c} (h : Represents raw p w d c) (e : Extends raw p q) :
    Represents raw q w d c :=
  ⟨h.bucket.mono e, List.Forall₂.imp (fun _ _ v => v.mono e) h.leaves,
   List.Forall₂.imp (fun _ _ v => v.mono e) h.depths⟩

private def step (row : Row) (rem : Word) : Build (Word × Digits) := do
  let (afterDepth, digits) ← divmod rem row.depthCount
  let (afterSupport, support) ← divmod afterDepth row.supports
  let (rest, bucket) ← divmod afterSupport row.buckets
  let leaves ← unrank row.t row.k support
  let depths ← DepthGaps.wordProgram row digits
  return (rest, ⟨bucket, leaves, depths⟩)

private def loop (row : Row) (indices : List Nat) (rem0 : Word) (coords0 : List Digits) :
    Build (Word × List Digits) := do
  let mut rem := rem0
  let mut coords := coords0
  for _ in indices do
    let (rest, coord) ← step row rem
    rem := rest
    coords := coord :: coords
  return (rem, coords)

private theorem program (row : Row) :
    decode row = (do
      let a ← loadRaw row.r (width row)
      let (rem, coords) ← loop row (List.range row.K) a []
      let valid ← eqw rem (lit (width row) 0)
      return (valid, coords.reverse)) := by
  rw [loadRaw_loop]
  by_cases hc : row.cap = 0 <;>
    simp [decode, loop, step, DepthGaps.wordProgram, DepthGaps.loop, hc,
      Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, List.range_eq_range']

/-- Sufficient arithmetic hypotheses for one coordinate of this concrete decoder. -/
structure RowSpec (row : Row) (depths : Nat → List Nat) : Prop where
  depth_pos : 0 < row.depthCount
  depth_guard : 2*row.depthCount ≤ 2^width row
  support_pos : 0 < row.supports
  support_guard : 2*row.supports ≤ 2^width row
  bucket_pos : 0 < row.buckets
  bucket_guard : 2*row.buckets ≤ 2^width row
  leaves_ok : ∀ {raw p a r}, Seeded raw p → Holds raw p (width row) a r → r < row.t.choose row.k →
    Builds raw p (unrank row.t row.k a) (fun q out =>
      List.Forall₂ (Holds raw q (width row)) out (Colex.digits row.t row.k r).reverse)
  depths_ok : ∀ {raw p a r}, Seeded raw p → Holds raw p (width row) a r → r < row.depthCount →
    Builds raw p (DepthGaps.wordProgram row a) (fun q out =>
      List.Forall₂ (Holds raw q (width row)) out (depths r))

private theorem step_spec {row depths raw p rem x} (sp : RowSpec row depths) (s : Seeded raw p)
    (hrem : Holds raw p (width row) rem x) :
    Builds raw p (step row rem) (fun q pair =>
      Holds raw q (width row) pair.1 (x / radix row) ∧
      Represents raw q (width row) pair.2 (coordinate row depths x)) := by
  unfold step
  refine (divmod_nat s hrem _ sp.depth_pos sp.depth_guard).bind ?_
  intro q1 z1 e1 hz1
  rcases z1 with ⟨afterDepth, digits⟩
  obtain ⟨h1, hd⟩ := hz1
  refine (divmod_nat (s.mono e1) h1 _ sp.support_pos sp.support_guard).bind ?_
  intro q2 z2 e2 hz2
  rcases z2 with ⟨afterSupport, support⟩
  obtain ⟨h2, hs⟩ := hz2
  have e02 := e1.trans e2
  refine (divmod_nat (s.mono e02) h2 _ sp.bucket_pos sp.bucket_guard).bind ?_
  intro q3 z3 e3 hz3
  rcases z3 with ⟨rest, bucket⟩
  obtain ⟨h3, hb⟩ := hz3
  have e03 := e02.trans e3
  have hchoose : x / row.depthCount % row.supports < row.t.choose row.k := by
    rw [Nat.choose_eq_fast_choose]
    exact Nat.mod_lt _ sp.support_pos
  refine (sp.leaves_ok (s.mono e03) (hs.mono e3) hchoose).bind fun q4 leaves e4 hl => ?_
  have e04 := e03.trans e4
  refine (sp.depths_ok (s.mono e04) (hd.mono ((e2.trans e3).trans e4))
    (Nat.mod_lt _ sp.depth_pos)).bind fun q5 depthWords e5 hdepth => ?_
  apply builds_pure
  have e35 := e4.trans e5
  exact ⟨by simpa only [radix, Nat.div_div_eq_div_mul] using h3.mono e35,
    ⟨hb.mono e35, List.Forall₂.imp (fun _ _ h => h.mono e5) hl, hdepth⟩⟩

private theorem loop_spec {row depths raw} (sp : RowSpec row depths)
    (indices : List Nat) (p : Array Gate) (rem : Word) (x : Nat) (acc : List Digits) (prev : List Coordinate)
    (s : Seeded raw p) (hrem : Holds raw p (width row) rem x)
    (ha : List.Forall₂ (Represents raw p (width row)) acc prev) :
    Builds raw p (loop row indices rem acc) (fun q z =>
      Holds raw q (width row) z.1 (x/(radix row)^indices.length) ∧
      List.Forall₂ (Represents raw q (width row)) z.2
        ((coordinates row depths indices.length x).reverse ++ prev)) := by
  induction indices generalizing p rem x acc prev with
  | nil =>
    simpa [loop, coordinates] using (builds_pure (raw := raw) (x := (rem,acc))
      (post := fun q z => Holds raw q (width row) z.1 x ∧
          List.Forall₂ (Represents raw q (width row)) z.2 prev) ⟨hrem, ha⟩)
  | cons i is ih =>
    have he : loop row (i :: is) rem acc = (do
        let z ← step row rem
        loop row is z.1 (z.2 :: acc)) := by
      simp [loop]
    rw [he]
    refine (step_spec sp s hrem).bind fun q pair e h => ?_
    have saved := List.Forall₂.cons h.2 (List.Forall₂.imp (fun _ _ z => z.mono e) ha)
    have hpow : radix row * (radix row)^is.length = (radix row)^(is.length+1) := by
      rw [Nat.pow_succ, Nat.mul_comm]
    simpa only [List.length_cons, coordinates, Nat.div_div_eq_div_mul, hpow, List.reverse_cons,
      List.append_assoc, List.singleton_append] using
      ih q pair.1 (x/radix row) (pair.2::acc) _ (s.mono e) h.1 saved

def Spec (row : Row) (depths : Nat → List Nat) (raw : Nat) (q : Array Gate)
    (result : Nat × List Digits) : Prop :=
  HasBit raw q result.1 (decide (raw < row.domain)) ∧
    List.Forall₂ (Represents raw q (width row)) result.2 (coordinates row depths row.K raw)

theorem decode_spec {row depths raw p} (sp : RowSpec row depths) (s : Seeded raw p) (hr : raw < 2^row.r) :
    Builds raw p (decode row) (Spec row depths raw) := by
  rw [program]
  have hwidth : row.r ≤ width row := (Nat.le_add_right row.r 2).trans (Nat.le_max_left ..)
  have load := loadRaw_nat s row.r (width row) hwidth
  rw [Nat.mod_eq_of_lt hr] at load
  refine load.bind fun q a e hword => ?_
  refine (loop_spec sp (List.range row.K) q a raw [] [] (s.mono e) hword .nil).bind ?_
  intro v pair f hp
  rcases pair with ⟨rem, coords⟩
  obtain ⟨hquot, hcoords⟩ := hp
  have sv := s.mono (e.trans f)
  have hdomain : (radix row)^row.K = row.domain := by
    unfold radix Row.domain
    rw [Nat.mul_comm (row.depthCount * row.supports), Nat.mul_comm row.depthCount,
      Nat.mul_assoc]
  simp only [List.length_range, hdomain, List.append_nil] at hquot hcoords
  have zero : Holds raw v (width row) (lit (width row) 0) 0 := by
    simpa only [Nat.zero_mod] using holds_literal sv (width row) 0
  have eqwSpec := LiteralMaskSemantics.eqw_number sv
    (show LiteralMaskSemantics.Number raw v (width row) rem (raw/row.domain) from
      ⟨hquot.size, hquot.valid, hquot.value_eq⟩)
    (show LiteralMaskSemantics.Number raw v (width row) (lit (width row) 0) 0 from
      ⟨zero.size, zero.valid, zero.value_eq⟩)
  refine eqwSpec.bind fun final valid g hv => ?_
  apply builds_pure
  have hd : 0 < row.domain := by
    rw [← hdomain]
    exact Nat.pow_pos (Nat.mul_pos (Nat.mul_pos sp.depth_pos sp.support_pos) sp.bucket_pos)
  have hrev : List.Forall₂ (Represents raw v (width row)) coords.reverse
      (coordinates row depths row.K raw) := by simpa using DepthGaps.reverse_related hcoords
  exact ⟨by simpa only [Nat.div_eq_zero_iff_lt hd] using hv,
    List.Forall₂.imp (fun _ _ z => Represents.mono z g) hrev⟩

def bucketDepths (_ : Nat) : List Nat := List.replicate BucketRefined.p.k 0

private theorem bucketRow : RowSpec BucketRefined.p bucketDepths where
  depth_pos := by decide +kernel
  depth_guard := by decide +kernel
  support_pos := by decide +kernel
  support_guard := by decide +kernel
  bucket_pos := by decide +kernel
  bucket_guard := by decide +kernel
  leaves_ok := RowUnrank.bucket_support
  depths_ok := fun s _ _ => DepthGaps.bucket_program s

private theorem chainRow : RowSpec ChainRefined.p DepthGaps.chainValues where
  depth_pos := by decide +kernel
  depth_guard := by decide +kernel
  support_pos := by decide +kernel
  support_guard := by decide +kernel
  bucket_pos := by decide +kernel
  bucket_guard := by decide +kernel
  leaves_ok := RowUnrank.chain_support
  depths_ok := DepthGaps.chain_program

theorem decode_bucket {raw p} (s : Seeded raw p) (hr : raw < 2^BucketRefined.p.r) :
    Builds raw p (decode BucketRefined.p) (Spec BucketRefined.p bucketDepths raw) :=
  decode_spec bucketRow s hr

theorem decode_chain {raw p} (s : Seeded raw p) (hr : raw < 2^ChainRefined.p.r) :
    Builds raw p (decode ChainRefined.p) (Spec ChainRefined.p DepthGaps.chainValues raw) :=
  decode_spec chainRow s hr

end PoissonDAG.PORS.RankGates.MixedDecode
