import YM.FVA2.Change.Clock
/-! # Exact physical cylinder addresses -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Change
open Function Set Filter Finset Lattice MeasureTheory
open MS MS.Koszul MS.Plane MS.Orbit Cog Orbit.LogReal MS.Swirl MS.Book Convolve Program
open MS.Puff MS.Puff.Mom MS.Puff.Engine MS.Puff.Actors
open MS.Swirl.Near MS.Native Wilsonian Chart MS.Bare MS.Landau MS.Cylinder Lab Taylor
open Slice Fourier Wilson
open scoped BigOperators Topology ContDiff
variable {G:Gauge}{n:Side}
local notation "T" => Site n

/-- Proof-bearing stencil of the regulator prescription. `obs` is an actual group
observable at the origin. It can be specified, e.g., by wrapping the finite transported stencil
in the appropriate Wilson dictionary. Require the *whole germ* on the full n-torus in the MS
basis, before hitting with the gauge-fixed Fourier line.

This type is agnostic on selection (caller will give one such realization per stamp in
`MS.Menus.LitBook`). Can share any one prescription across arities, orders and geometries. -/
structure Stencil (F : Dot G Cover) where
  obs (n:Side) : Wilson.Config G n → ℝ
  gauge (n:Side) : Lattice.GaugeInvariant (obs n)
  smooth (n:Side) : germ (obs n ∘ nation)
  continuous (n:Side) : Continuous (obs n)
  billable (n:Side) : enters n F=reads (obs n ∘ nation)

variable {F:Dot G Cover}
namespace Stencil
variable (p : Cover) (X: Stencil F)

def placed (n:Side)(p:Cover) : Wilson.Config G n→ℝ:= X.obs n ∘ Lattice.translate (wrap n p)
lemma invariant : Lattice.GaugeInvariant (X.placed n p) := by
  intro t U; unfold placed; simp only [comp_apply]
  rw [show Lattice.translate (wrap n p) (Lattice.gauge t U)=Lattice.gauge (fun x=>t (x+wrap n p)) (Lattice.translate (wrap n p) U) from funext fun i=>by simp [Lattice.translate,Lattice.gauge,add_right_comm]]; exact X.gauge n ..
lemma continuous_placed : Continuous (X.placed n p) := (X.continuous n).comp (continuous_pi (fun _=>continuous_apply (A:=fun _ : Edge T=>G.El) _))

def turn (s:T) : Chart.City G T→L[ℝ] Chart.City G T := ContinuousLinearMap.pi fun i=> ContinuousLinearMap.proj (s+i.1,i.2)
lemma at_places : X.placed n p ∘ nation = X.obs n ∘ nation ∘ turn (wrap n p):= by
  funext a; unfold placed; simp only [comp_apply]; apply congr_arg (X.obs n); funext x; simp [Lattice.translate]; rw [add_comm x.1]; rfl
lemma crease : germ (X.placed n p∘ nation) := by
  rw [at_places]; let L:= (turn (G:=G) (wrap n p)); show germ ((X.obs n ∘ nation) ∘ L); exact (show ContDiffAt ℝ ω _ (L 0) from L.map_zero.symm ▸ X.smooth n).comp 0 L.contDiff.contDiffAt

-- `Lab.Shift` on full local modes at the stencil origin; reflection not applied
lemma turned (s:T)(a:FixedMode G n) : turn s (direction (post (fun x:T=>s+x) a)) = direction a:= by
  rcases a with ⟨⟨⟨_|j,_|_⟩,i⟩,t⟩
  all_goals first | exact map_zero (turn s) | skip
  funext ⟨x,h⟩; change priv ((s+t,j),i) (s+x,h) = priv ((t,j),i) (x,h); simp [priv,Pi.single_apply]

lemma travel_bill : enters n (Lab.Shift p F)= reads (X.placed n p ∘ nation) := by
  let T' := wrap n p; let J:= Lab.post (fun x:T=>T'+x) (A:=Branch G Axis)
  let e : FixedMode G n ≃ FixedMode G n:= (Equiv.refl _).prodCongr (Equiv.addLeft T')
  have he (i:FixedMode G n): e i=J i:=rfl
  funext l; let i : List (FixedMode G n):= l.map e.symm
  have hT : i.map J=l := by simp only [i, ← funext he,List.map_map,Equiv.self_comp_symm,List.map_id]
  rw [← hT, at_places]; change (transport (wrap n) (Lab.Shift p F)).val _ = _
  rw [trans_shift]; change (Ferry J (shown n F)).val _ = ink _ _ _
  have hp : Injective J:= (show (⇑e)=J from funext he) ▸ e.injective
  rw [without J (shown n F) hp]; rw [show ink direction (X.obs n ∘ nation ∘ turn T')= _ from ink_ctrl_one (direction (G:=G)) (turn T') (X.smooth n)]
  rw [show (shown n F).val=reads (X.obs n ∘ nation) from X.billable n]
  suffices h : ∀ (i:List (FixedMode G n)) (f:Chart.City G T → ℝ),ink (turn T' ∘ direction (G:=G)) f (i.map J)= ink direction f i from (h _ _).symm
  intro i f; induction i generalizing f with| nil=> rfl| cons a i ih=> rw [List.map_cons]; change ink _ (layer (turn T' (direction _)) _) _ = ink _ (layer (direction _) _) _; rw [turned]; exact ih _
end Stencil
end YM.FVA2.Change
