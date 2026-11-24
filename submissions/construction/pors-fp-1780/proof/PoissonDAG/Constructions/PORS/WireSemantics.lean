import PoissonDAG.Constructions.PORS.WireRender

namespace PoissonDAG.PORS

/-- Reading a translated address gives the original value, including the
false returned by the protected evaluator for an out-of-range address. -/
theorem get_wireRef (values : List Bool) (source : Nat) :
    get (false :: values) (wireRef values.length source) = get values source := by
  by_cases h : source < values.length
  · simp [wireRef, h, get]
  · simp [wireRef, h, get]

/-- The renderer keeps exactly the low input bits and preserves all gate
operations on the already evaluated wires. -/
theorem evalGate_renderGate (raw width bound : Nat) (values : List Bool)
    (hlen : values.length = bound) (g : Gate) :
    evalGate raw (false :: values) (renderGate width bound g) =
      evalGate (raw % 2^width) values g := by
  subst bound
  cases g with
  | input j =>
    by_cases h : j < width <;> simp [renderGate, h, evalGate, Nat.testBit_mod_two_pow]
  | constant b => rfl
  | neg a => simp [renderGate, evalGate, get_wireRef]
  | conj a b => simp [renderGate, evalGate, get_wireRef]
  | xor a b => simp [renderGate, evalGate, get_wireRef]

private theorem execute_append_one (raw : Nat) (gs : List Gate) (g : Gate) :
    executeGates raw (gs ++ [g]) =
      executeGates raw gs ++ [evalGate raw (executeGates raw gs) g] := by
  simp [executeGates, List.foldl_append]

theorem executeGates_length (raw : Nat) (gs : List Gate) :
    (executeGates raw gs).length = gs.length := by
  suffices h : ∀ (todo : List Gate) (values : List Bool),
      (todo.foldl (fun xs g => xs ++ [evalGate raw xs g]) values).length =
        values.length + todo.length by
    simpa [executeGates] using h gs []
  intro todo
  induction todo with
  | nil => intro values; simp
  | cons g rest ih =>
    intro values
    simp [ih, Nat.add_comm, Nat.add_left_comm]

private theorem execute_render_prefix (raw width : Nat) (gateAt : Nat → Gate) (n : Nat) :
    executeGates raw (.constant false :: (List.range n).map
      (fun i => renderGate width i (gateAt i))) =
      false :: executeGates (raw % 2^width) ((List.range n).map gateAt) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hlen : (executeGates (raw % 2^width) ((List.range n).map gateAt)).length = n := by
      simp [executeGates_length]
    rw [List.range_succ]
    simp only [List.map_append, List.map_singleton]
    change executeGates raw ((.constant false :: _) ++ [_]) =
      false :: executeGates (raw % 2^width) (_ ++ [_])
    rw [execute_append_one, execute_append_one, ih]
    rw [evalGate_renderGate raw width n _ hlen] <;> rfl

private theorem indexed_gates (p : Array Gate) :
    (List.range p.size).map (fun i => p[i]?.getD (.constant false)) = p.toList := by
  apply List.ext_getElem
  · simp
  · intro i hi _
    have h : i < p.size := by simpa using hi
    simp [Array.getElem?_eq_getElem h]

/-- The full protected trace is the leading sentinel followed by the source
program's trace on the width-bit input, for every program and every raw word. -/
theorem executeGates_render (raw width outputCount : Nat) (p : Array Gate) (wires : List Nat) :
    executeGates raw (render width outputCount p wires).gates =
      false :: executeGates (raw % 2^width) p.toList := by
  simpa only [render, indexed_gates] using
    execute_render_prefix raw width (fun i => p[i]?.getD (.constant false)) p.size

/-- An output list of arbitrary declared length is read from the source trace.
A missing output address reads the wire just past the end, hence false. -/
theorem render_eval (raw width outputCount : Nat) (p : Array Gate) (wires : List Nat) :
    (render width outputCount p wires).eval raw =
      (List.range outputCount).map (fun i =>
        get (executeGates (raw % 2^width) p.toList) (wires[i]?.getD p.size)) := by
  change (render width outputCount p wires).outputs.map
    (get (executeGates raw (render width outputCount p wires).gates)) = _
  rw [executeGates_render]
  simp only [render, List.map_map, List.getElem?_toArray]
  apply List.map_congr_left
  intro i _
  have hlen : (executeGates (raw % 2^width) p.toList).length = p.size := by
    simp [executeGates_length]
  simpa only [hlen, Function.comp_apply] using
    get_wireRef (executeGates (raw % 2^width) p.toList) (wires[i]?.getD p.size)

/-- On full-arity output lists and challenge-domain inputs, rendering preserves
the original circuit's protected Boolean output exactly. -/
theorem render_eval_eq_source (raw width : Nat) (p : Array Gate) (wires : List Nat)
    (hraw : raw < 2^width) :
    (render width wires.length p wires).eval raw =
      (Circuit.mk width p.toList wires).eval raw := by
  rw [render_eval, Nat.mod_eq_of_lt hraw]
  change _ = wires.map (get (executeGates raw p.toList))
  apply List.ext_getElem
  · simp
  · intro i hi _
    have h : i < wires.length := by simpa using hi
    simp [List.getElem?_eq_getElem h]

end PoissonDAG.PORS
