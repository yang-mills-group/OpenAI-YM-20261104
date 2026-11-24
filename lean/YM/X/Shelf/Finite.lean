import YM.X.Shelf.Pebble
import Mathlib.LinearAlgebra.Dual.Lemmas
/-!
# sensor banks. Scalar crew submodules define canonical Steady from testing. Useful if unscaled gauge-variant coordinates to be priced. 
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Shelf
open Lattice Wilson Next.Rank Interval PertExtension LatticePT Filter Set Function Metric MeasureTheory Asymptotics Reed Size
open scoped Topology ContDiff BigOperators Classical
variable {V W I:Type*}
variable [AddCommGroup V][Module ℂ V]
local notation "D"=> Module.Dual
local notation "L"=> (atTop:Filter ℕ)
section sep
variable [FiniteDimensional ℂ V]
lemma multitude (F:I→D ℂ V)(hl:∀ x:V,(∀ i,F i x=0)→ x=0) (f:ℕ→V)(P:Submodule ℂ (ℕ→ℂ))(he:∀ i,(fun k=> F i (f k))∈P) : f ∈ Badge V (fun x=>x∈ P) ⊤:= by
   let S:= Submodule.span ℂ (range F); have hx(x:V)(h:x∈ S.dualCoannihilator): x=0:= hl x (fun i=> Submodule.mem_dualCoannihilator x|>.mp h (F i) (Submodule.subset_span ⟨i,rfl⟩))
   have hg:S=⊤:= by rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W:=S),show S.dualCoannihilator=⊥ from bot_unique (fun x hx'=>hx x hx'), Submodule.dualAnnihilator_bot]
   have he (l:D ℂ V): (fun k=> l (f k))∈P:= by
      have H:l∈S:= hg ▸ Submodule.mem_top
      induction H using Submodule.span_induction with
      | mem p h=> obtain ⟨i,rfl⟩:=h; exact he i
      | zero=> simp only [LinearMap.zero_apply]; exact Submodule.zero_mem P
      | add a b h h' ih ih'=> simp_rw [LinearMap.add_apply]; exact Submodule.add_mem _ ih ih'
      | smul x a _ h=> simp_rw [LinearMap.smul_apply]; exact Submodule.smul_mem _ x h
   let b:= Module.finBasis ℂ V; let I:= Fin (Module.finrank ℂ V); have hx : f=∑ i:I,(fun k=>b.coord i (f k) • b i):= funext fun k=> by rw [Finset.sum_apply]; exact (b.sum_repr ..).symm
   rw [hx]; exact Submodule.sum_mem _ (fun i hi=> badged _ (he (b.coord i)) Submodule.mem_top) -- rewrites both occurrences?
end sep
lemma plenty (F:I→D ℂ V)(A:Submodule ℂ V)[FiniteDimensional ℂ A](hl:∀ x∈A,(∀ i,F i x=0)→ x=0)(f:ℕ→V)(hf: ∀ i,f i ∈ A)(P: Submodule ℂ (ℕ→ℂ))(he:∀ i,(fun k=> F i (f k))∈P): f∈ Badge V (fun x=>x∈ P) A:= by
   let g(i:ℕ):A:=⟨f i,hf i⟩; let H(i:I):= (F i) ∘ₗ A.subtype
   have hx : ∀ x:A,(∀ i,H i x=0)→ x=0:= fun x h=> Subtype.ext (hl x.val x.property h)
   exact moved A.subtype (fun x _=> x.property) (multitude H hx g P he)

def fades (V:Type*) [NormedAddCommGroup V][NormedSpace ℂ V]: Submodule ℂ (ℕ→ V) where
   carrier:={p| Tendsto p atTop (𝓝 0)}
   smul_mem' a p h:= by simpa using! ((show Tendsto _ _ (𝓝 (0:V)) from h).const_smul a)
   zero_mem':= tendsto_const_nhds
   add_mem' {p q} h hq:=by simpa only [add_zero] using! (Tendsto.add h (show Tendsto _ _ (𝓝 (0:V)) from hq))
lemma fading {f:ℕ→ℂ}(h:f∈ fades ℂ):Tendsto f L (𝓝 0):= h

def crew : Submodule ℂ (ℕ→ℂ) where
   carrier:={p|Released p}
   smul_mem' c p h:= breaths (constell c) h
   zero_mem':=Released.zero
   add_mem' := fun _ _=> Released.add (by assumption) (by assumption)
lemma decor {A:Submodule ℂ V}{P:ℕ→V}{F:V→ₗ[ℂ]ℂ} (h:P ∈ Badge V (fun x=>x∈ fades ℂ) A): Tendsto (fun i=> F (P i)) L (𝓝 0):= by
    induction h using Submodule.span_induction with
    | mem y h=> obtain ⟨c,v,H,hv,rfl⟩:=h; simp_rw [map_smul]; simpa only [zero_smul] using! ((fading H).smul_const (F v))
    | zero=> simp_rw [Pi.zero_apply,map_zero]; exact tendsto_const_nhds
    | add a b h p x y=> simp_rw [Pi.add_apply,map_add]; simpa only [zero_add] using! x.add y
    | smul a b h y=> simp_rw [Pi.smul_apply,map_smul]; simpa only [smul_zero] using! y.const_smul a -- simpler
end YM.PositionX.Shelf
