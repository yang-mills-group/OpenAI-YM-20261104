import YM.RG12.Strike.Writing
/-! # Uniform letterbox, strict ordering of all but the leading angular term

Use displacement derivative order; signs for differentiating at an external *mark* against displacement from
vertex TO mark can be added via end family; don't equate lattice and continuum.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Strike
open Function Set Filter MeasureTheory Real
open scoped Topology InnerProductSpace ContDiff BigOperators Classical

abbrev Poke := Cells
-- left composition directional maps
def barrage (f:R→ℂ):Cells→R→ℂ
 | []=> f
 | i::b=> hit i (barrage f b)
def flint (i:Axis4): List Stroke→ List Stroke
 | [] => []
 | a::b => flourish i a ++ flint i b
variable (i:Axis4)
lemma flintAt (L:List Stroke){x:R}(he:x≠0): HasDerivAt (scripts L ∘ palette i x) (scripts (flint i L) x) 0:=by
   induction L with
   | nil=>simpa [scripts,flint,comp_def] using (hasDerivAt_const (0:ℝ) (0:ℂ))
   | cons a l h=> rw [flint, scripts_swing]; exact (changeAt i x a he).add h
lemma flint_length (L:List Stroke)(d:ℕ)(h:∀ a∈L,a.deck.length<d): ∀ a∈ flint i L,a.deck.length<d+1:=by
   induction L with
   | nil=> simp [flint]
   | cons a b he=>
     intro v hv; obtain h'|h':=(List.mem_append.mp (by exact hv)) -- hv defexpand needed
     · obtain rfl|hs:= List.mem_cons.mp (by exact h' : v∈ _::_) -- specify type
       · change a.deck.length+1< d+1; exact Nat.succ_lt_succ (h _ List.mem_cons_self)
       obtain ⟨z,hz,he⟩:=List.mem_map.mp hs; subst v; exact (trims _ _ _ hz).trans (by have ht:=h a List.mem_cons_self; omega)
     · exact he (fun j hj=> h j (List.mem_cons_of_mem a hj)) v h'

-- continuum Feynman line. normalization optional due homology.
def field (x:R):ℂ:= (black x)⁻¹
def coefficient : ℕ→ℂ
 | 0 =>1
 | i+1=> -(2*(↑i+1))*coefficient i -- n+1

def pin (L:Poke):Stroke:=⟨coefficient L.length,L.length+1,L⟩
def bottom (i:Axis4)(a:Stroke):List Stroke:= (pluck i a.deck).map (fun p=> Stroke.mk a.weight a.rate p)
lemma bloom (L:Poke): flourish i (pin L)=pin (i::L):: bottom i (pin L):=by simp [coefficient,pin,flourish,bottom]
-- expansion uniform orthogonal charge
theorem fire (L:Poke):∃ S:List Stroke, (∀ x∈ S,x.deck.length<L.length)∧∀ x:R,x≠0→ barrage field L x=scripts (pin L::S) x:=by
   induction L with
   | nil => exact ⟨[],by simp,fun x _=>by simp [pin,scripts,drip,barrage,field,sun_nil,coefficient]⟩
   | cons i L H=>
      obtain ⟨W,hW,he⟩:=H
      refine ⟨bottom i (pin L) ++ flint i W,fun a ha=> ?_,fun x hx=> ?_⟩
      · obtain h|h' :=List.mem_append.mp ha
        · obtain ⟨z,hz,rfl⟩:=List.mem_map.mp h
          exact (trims i L z hz).trans (by simp)
        exact flint_length _ W L.length hW _ h'
      have ht: (barrage field L ∘ palette i x) =ᶠ[𝓝 (0:ℝ)] (scripts (pin L::W) ∘ palette i x):=by
         have hv : Tendsto (palette i x) (𝓝 (0:ℝ)) (𝓝 x):=by convert (show Continuous (palette i x) from by unfold palette; fun_prop).continuousAt (x:=0).tendsto; simp [palette]
         filter_upwards [hv.eventually_ne hx] with t ht using he _ ht
      have hs: hit i (barrage field L) x= scripts (flint i (pin L::W)) x:=((flintAt i _ hx).congr_of_eventuallyEq ht).deriv
      simpa only [barrage,flint,bloom,List.cons_append] using! hs

end YM.RG12.Strike
