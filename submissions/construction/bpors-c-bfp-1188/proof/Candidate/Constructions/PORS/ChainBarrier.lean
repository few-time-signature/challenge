import Candidate.Constructions.PORS.BucketSource
import Candidate.Constructions.PORS.ChainLeafOpening

section

namespace PoissonDAG.PORS.ChainPositions

open BucketSource

theorem atBlock_add (unit : Tree) (s : Shape) (i v : Nat) :
    atBlock unit s i v=atBlock unit s i 0+v := by
  induction s generalizing i with
  | leaf => simp [atBlock]
  | branch l r il ir =>
    by_cases h : i<l.leaves
    · simp only [atBlock,if_pos h,il i]
    · simp only [atBlock,if_neg h,ir (i-l.leaves),Nat.add_assoc]

/-- Inside a binary arrangement of blocks, the emitted node is the node at
the same local index in the single block with the corresponding address base. -/
theorem emit_block (unit : Tree) (s : Shape) (base i v : Nat) (hi : i<s.leaves)
    (hv : v+1<unit.nodes) :
    ((s.fill unit).emit base)[atBlock unit s i v]? = (unit.emit (base+atBlock unit s i 0))[v]? := by
  induction s generalizing i base with
  | leaf => simp [Shape.fill,atBlock]
  | branch l r il ir =>
    change i < l.leaves+r.leaves at hi
    let L := (l.fill unit).emit base
    let R := (r.fill unit).emit (base+(l.fill unit).nodes)
    let root := Node.binary (base+(l.fill unit).nodes-1) (base+(l.fill unit).nodes+(r.fill unit).nodes-1)
    change ((L++R)++[root])[atBlock unit (.branch l r) i v]? = _
    by_cases h : i<l.leaves
    · have lt : atBlock unit l i v<L.length := by
        have hint := interior unit l h hv
        change _<((l.fill unit).emit base).length
        rw [Tree.emit_length]; omega
      simp only [atBlock,if_pos h,List.getElem?_append_left (show atBlock unit l i v < (L++R).length by
        simp only [List.length_append]; omega),List.getElem?_append_left lt]
      exact il base i h
    · have sub : i-l.leaves<r.leaves := by omega
      have lt : atBlock unit r (i-l.leaves) v<R.length := by
        have hint := interior unit r sub hv
        change _<((r.fill unit).emit _).length
        rw [Tree.emit_length]; omega
      have len : L.length=(l.fill unit).nodes := Tree.emit_length _ _
      simp only [atBlock,if_neg h,←len]
      rw [List.getElem?_append_left (by simp only [List.length_append]; omega),
        List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]
      simpa only [len,Nat.add_assoc] using ir (base+(l.fill unit).nodes) (i-l.leaves) sub

private theorem chain_node (n base v : Nat) (hv : v ≤ n) :
    ((chain n).emit base)[v]? = some (if v=0 then .source else .unary (base+v-1)) := by
  induction n with
  | zero =>
    have h : v=0 := by omega
    subst v
    rfl
  | succ n ih =>
    change ((chain n).emit base ++ [.unary (base+(chain n).nodes-1)])[v]?=_
    by_cases h : v ≤ n
    · rw [List.getElem?_append_left (by rw [Tree.emit_length,chain_nodes]; omega)]
      exact ih h
    · have eq : v=n+1 := by omega
      subst v
      rw [List.getElem?_append_right (by rw [Tree.emit_length,chain_nodes])]
      simp [Tree.emit_length,chain_nodes]

/-- Absolute postorder position of chain slot v under the forest, bucket,
and selected leaf. -/
def vertex (f o c : Shape) (cap i b j v : Nat) :=
  let unit := chain (cap+1)
  let child := c.fill unit
  atBlock (o.fill child) f i (atBlock child o b (atBlock unit c j v))

theorem vertex_add (f o c : Shape) (cap i b j v : Nat) :
    vertex f o c cap i b j v=vertex f o c cap i b j 0+v := by
  unfold vertex
  let t := chain (cap+1)
  let C := c.fill t
  let O := o.fill C
  change atBlock O f i (atBlock C o b (atBlock t c j v)) =
    atBlock O f i (atBlock C o b (atBlock t c j 0))+v
  rw [atBlock_add O f i (atBlock C o b (atBlock t c j v)),
    atBlock_add O f i (atBlock C o b (atBlock t c j 0)),
    atBlock_add C o b (atBlock t c j v),atBlock_add C o b (atBlock t c j 0),
    atBlock_add t c j v]
  omega

theorem below (f o c : Shape) (cap i b j v : Nat) (hi : i<f.leaves) (hb : b<o.leaves)
    (hj : j<c.leaves) (hv : v ≤ cap) : vertex f o c cap i b j v+1 < (graph f o c cap).length := by
  unfold graph
  rw [Tree.emit_length]
  exact interior _ f hi (interior _ o hb (interior _ c hj (by rw [chain_nodes]; omega)))

theorem node (f o c : Shape) (cap i b j v : Nat) (hi : i<f.leaves) (hb : b<o.leaves)
    (hj : j<c.leaves) (hv : v ≤ cap) :
    (graph f o c cap)[vertex f o c cap i b j v]? =
      some (if v=0 then .source else .unary (vertex f o c cap i b j 0+v-1)) := by
  let t := chain (cap+1)
  let C := c.fill t
  let O := o.fill C
  have vt : v+1<t.nodes := by change _ < (chain (cap+1)).nodes; rw [chain_nodes]; omega
  have vc := interior t c hj vt
  have vo := interior C o hb vc
  change ((f.fill O).emit 0)[atBlock O f i (atBlock C o b (atBlock t c j v))]? = _
  rw [emit_block O f 0 _ _ hi vo,Nat.zero_add,emit_block C o _ _ _ hb vc,emit_block t c _ _ _ hj vt]
  rw [chain_node _ _ _ (by omega)]
  have eq : vertex f o c cap i b j 0 = atBlock O f i 0+atBlock C o b 0+atBlock t c j 0 := by
    change atBlock O f i (atBlock C o b (atBlock t c j 0))=_
    rw [atBlock_add O f i (atBlock C o b (atBlock t c j 0)),atBlock_add C o b (atBlock t c j 0)]
    omega
  rw [eq]

end PoissonDAG.PORS.ChainPositions
end

section

namespace PoissonDAG.PORS.ChainPositions

open ChainLeafGates
open BucketSource (bit through interior)

/-- The disclosed chain label is precisely the one at the stopping position. -/
private theorem stop_bit (cap e v : Nat) :
    bit (some (openChain (cap+1) (cap-e))) v = decide (v=cap-e) := by
  let t := cap-e
  have ht : t ≤ cap := Nat.sub_le ..
  have he : t+(cap+1-t)=cap+1 := by omega
  have hm := openChain_marks t (cap+1-t)
  rw [he] at hm
  change get ((openChain (cap+1) t).marks.map Prod.fst) v=decide (v=t)
  rw [hm]
  by_cases h : v=t
  · subst v
    simp [oneLabel,get]
  · by_cases lt : v<t
    · simp [oneLabel,get,List.getElem?_append,lt,h]
    · simp [oneLabel,get,List.getElem?_append,lt,h]
      rw [show v-t=(v-(t+1))+1 by omega,List.getElem?_cons_succ,List.getElem?_replicate]
      split <;> rfl

/-- On the interior of a chain, precisely one postorder slot is transmitted,
and all three enclosing shapes preserve the selected coordinate, bucket, and leaf. -/
theorem mark_iff (f o c : Shape) (cap : Nat) (owner : Nat → Nat) (d : Nat → Nat → Option Nat)
    (i b j v : Nat) (hi : i<f.leaves) (hb : b<o.leaves) (hj : j<c.leaves) (hv : v ≤ cap) :
    bit (routedOpening f o c cap owner d) (vertex f o c cap i b j v)=true ↔
      b=owner i ∧ ∃ e, d i j=some e ∧ v=cap-e := by
  have iv : v+1<(chain (cap+1)).nodes := by rw [chain_nodes]; omega
  have cv := interior _ c hj iv
  have ov := interior _ o hb cv
  unfold vertex routedOpening
  rw [through _ _ f 0 i _ hi ov,Nat.zero_add i,through _ _ o 0 b _ hb cv,Nat.zero_add b]
  by_cases h : b=owner i
  · simp only [h,if_true,true_and]
    rw [through _ _ c 0 j v hj iv,Nat.zero_add j]
    cases hd : d i j with
    | none => simp [bit]
    | some e => simp [stop_bit]
  · simp [h,bit]

/-- Every label from the private source through the target stop depends only
on the previous label of that same chain. -/
theorem prefix_barrier (f o c : Shape) (cap i b j t : Nat) (hi : i<f.leaves) (hb : b<o.leaves)
    (hj : j<c.leaves) (ht : t ≤ cap) :
    GRSCC.BackwardBarrier (graph f o c cap) (fun w =>
      ∃ v ≤ t, vertex f o c cap i b j v=w) := by
  intro n w hm hw
  obtain ⟨v,hv,rfl⟩ := hw
  have hn := List.mk_mem_zipIdx_iff_getElem?.mp hm
  have eq := Option.some.inj (hn.symm.trans (node f o c cap i b j v hi hb hj (by omega)))
  subst n
  cases v with
  | zero => trivial
  | succ v =>
    simp only [Nat.succ_ne_zero,if_false,GRSCC.HasBlockedParent]
    refine ⟨v,by omega,?_⟩
    rw [vertex_add f o c cap i b j v]
    omega

/-- If the joint historical hash closure covers a target opening, each target
leaf has a historical supplier in the same coordinate and bucket. The supplier
offers a label at the same or an earlier chain position. -/
theorem supplier (s : Scheme) (f o c : Shape) (cap : Nat)
    (owner : Nat → Nat → Nat) (d : Nat → Nat → Nat → Option Nat)
    (graphEq : s.graph=graph f o c cap)
    (arity : s.encoder.outputs.length=1+2*s.graph.length)
    (routes : ∀ x ∈ s.accepted, ∃ a,
      routedOpening f o c cap (owner x) (d x)=some a ∧ s.frontier x=a.marks.map Prod.fst)
    {q : Nat} (h : Fin q → Fin s.accepted.length) (t : Fin s.accepted.length)
    (i j e : Nat) (hi : i<f.leaves) (hj : j<c.leaves)
    (hb : owner s.accepted[t] i<o.leaves) (chosen : d s.accepted[t] i j=some e) (he : e ≤ cap)
    (covered : s.covered (indexHistory s.accepted h) s.accepted[t]=true) :
    ∃ z : Fin q, owner s.accepted[h z] i=owner s.accepted[t] i ∧
      ∃ k, d s.accepted[h z] i j=some k ∧ e ≤ k := by
  let b := owner s.accepted[t] i
  let atPos := vertex f o c cap i b j
  let blocked := fun w => ∃ v ≤ cap-e, atPos v=w
  have mark (raw : Nat) (hr : raw∈s.accepted) (v : Nat) (hv : v ≤ cap) :
      get (s.frontier raw) (atPos v)=true ↔ b=owner raw i ∧ ∃ k, d raw i j=some k ∧ v=cap-k := by
    obtain ⟨a,rt,front⟩ := routes raw hr
    have m := mark_iff f o c cap (owner raw) (d raw) i b j v hi hb hj hv
    rw [rt] at m
    rw [front]
    exact m
  have bar : GRSCC.BackwardBarrier s.graph blocked := by
    rw [graphEq]
    exact prefix_barrier f o c cap i b j (cap-e) hi hb hj (by omega)
  have below' (v : Nat) (hv : v ≤ cap) : atPos v+1<s.graph.length := by
    rw [graphEq]
    exact below f o c cap i b j v hi hb hj hv
  have root : ¬blocked (s.graph.length-1) := by
    rintro ⟨v,hv,hpos⟩
    have hlt := below' v (by omega)
    omega
  have target := (mark s.accepted[t] (List.getElem_mem t.isLt) (cap-e) (by omega)).mpr
    ⟨rfl,e,chosen,rfl⟩
  obtain ⟨raw,hr,hit⟩ := GRSCC.covered_requires_barrier_hit s _ _ (atPos (cap-e)) arity bar root
    (by have := below' (cap-e) (by omega); omega) ⟨cap-e,le_rfl,rfl⟩ target covered
  obtain ⟨w,⟨v,hv,rfl⟩,front⟩ := GRSCC.not_avoids_witness hit
  obtain ⟨z,rfl⟩ := List.mem_ofFn.mp hr
  obtain ⟨bk,k,hk,pos⟩ := (mark _ (List.getElem_mem (h z).isLt) v (by omega)).mp front
  exact ⟨z,bk.symm,k,hk,by omega⟩

end PoissonDAG.PORS.ChainPositions
end
