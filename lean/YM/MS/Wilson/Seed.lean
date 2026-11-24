import YM.MS.Wilson.Splice
/-!
# Actual marks from pure gauge stencils

Guarded below by minimal rank. Terms linear-combinable in log. `Aura` for now only
 assumes from stencil evaluation all meshes. Later evaluate stencils in inversion.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Native.Studio
open Function Filter Set Finset Plane Koszul Cylinder Lab Taylor Lattice Native Bare Focus Landau Draft Sew Chart Wilsonian
open Book Convolve Program Paint Logarithm
open scoped Topology ContDiff
variable {G: Gauge} {n:ℕ} {F H: Dot G Cover} {q:ℤ}
-- `Aura` at every mesh. A' Uniform polynomial observable later.
structure Aura (F:Dot G Cover) (q:ℤ): Prop where
    low : From F.val q
    phase : Tuned F 0
    pay (k:Side) : ∃ f:(Edge (Site k)→ G.El)→ℝ, OpenGauge (drive k) f ∧ germ (f ∘ nation)∧ enters k F= reads (f ∘ nation)
namespace Aura
lemma sum {I:Type*} (J:Finset I){F:I→Dot G Cover}(h:∀i∈J,Aura (F i) q): Aura (∑ i∈J,F i) q:= by
    refine ⟨by rw [sum_stack]; exact From.sum _ (fun i hi=> (h i hi).low),Tune.sum J (fun i hi=> (h i hi).phase),fun k=>?_⟩
    classical
    choose! f hF hG h using fun i (hi:i∈J)=> (h i hi).pay k
    let Z:= ∑ i∈J,f i
    have he: Z ∘ nation= ∑ i∈J,(f i ∘ nation):= by funext a; simp [Z]
    refine ⟨Z,fun g U=> by simp only [Z,Finset.sum_apply]; exact Finset.sum_congr rfl fun i hi=>hF i hi g U,?_ ,?_⟩; rw [he]; exact (show germ (∑ i∈J,(f i ∘ nation)) from (by rw [funext (fun x=> Finset.sum_apply x J (fun i=>f i ∘ nation))]; exact ContDiffAt.sum hG)) -- name
    rw [map_sum,he,reads,ink_sum _ _ hG]; exact Finset.sum_congr rfl (fun i hi=> h i hi)
lemma add (hv:Aura F q)(hh:Aura H q): Aura (F+H) q := by
    refine ⟨hv.low.add hh.low,hv.phase.add hh.phase,fun k=>?_⟩; obtain ⟨f,h,hb,h'⟩:= hv.pay k; obtain ⟨g,hg,ha,H⟩:=hh.pay k; refine ⟨f+g,fun V W=> ?_, hb.add ha,?_⟩; exact congr_arg₂ (·+·) (h V W) (hg V W); rw [map_add,h',H]; exact (ink_add _ hb ha).symm
lemma scalar (c:ℝ)(h:Aura F q): Aura ((c:ℂ) • F) q:= by
    refine ⟨h.low.smul _, h.phase.cash _ (by simp), fun k=>?_⟩; obtain ⟨f,hV,hg,hH⟩:=h.pay k; refine ⟨c • f, fun V U=>congr_arg (c • ·) (hV V U), hg.const_smul c,?_⟩; rw [map_smul,hH]; exact (ink_smul _ hg c).symm
lemma zero (G:Gauge)(h:ℤ): Aura (0:Dot G Cover) h:= by refine ⟨fun _ _=>rfl,Tune.zero,fun k=> ⟨0,fun _ _=>rfl,contDiffAt_const,?_⟩⟩; change _=ink _ 0; rw [map_zero,ink_zero]
lemma lit (h:Aura F q): Colorless F:= by
    intro u; refine (markEq ..).mp ?_; refine Eventually.of_forall (fun k=>?_);
    obtain ⟨f,hf,hF,he⟩:=h.pay k; let P:=pull (G:=G) (P:=Site k) (A:=Edge (Site k)) id; let D:=art id (f ∘ nation); have ht : shown k F = D:= Subtype.ext (he.trans (Eq.symm (pooled id hF)))
    change transport _ _=_; rw [painting]; change dye u (shown k F)=_; rw [ht]; rw [art_roll _ _ _ hF]; congr 1; funext x; dsimp only [Function.comp_apply]; rw [show nation (roll u x)=siteGauge (drive k) (fun _=>u⁻¹) (nation x) from funext fun i=> (by simp [roll,nation,siteGauge,Maurer.runby]),hf]
lemma closed (H':G.Simple)(h:Aura F q): Weightless (Spectrum G) (core G) (levels q F):= by
    rw [scales]; intro l; refine Eventually.of_forall (fun k=>?_)
    obtain ⟨f,hf,hF,he⟩:=h.pay k; let P:= panel G (Site k); let B:= Paper G (Site k); let L:= docket k (W G); let R := docket k (Wilsonian.H G); let u:= enters k F;
    have hs := from_pass k h.low; have hx:= from_total k (presence G H'); have hE:= from_total k (mist G)
    have hm : u= ink (glow G (Site k)).e0 (f ∘ nation):= he
    have hS := confine (drive k) hf hF
    have hu : link B.BV true DotFlip L u=0:= by rw [show L= _ from witnessD k G,hm,(vibes (G:=G) (drive k)).onto _ hF]; simp_rw [inkit _ (hS _),ink_zero,map_zero,Finset.sum_const_zero]
    have hR : link B.BV true DotFlip R u=0:= by rw [show R= _ from shiftD k G,hm]; exact link_g ..
    have hv : B.BV u=0:= by rw [hm]; exact lap_g ..
    rw [core,map_add]; -- edit
    let V:=tokenL B.BV true DotFlip;
    rw [show promote (docket k) (levels 2 (W G)) = rankLevel 2 L from level_up _ _ _ true, show promote (docket k) _ = rankLevel 0 R from level_up _ _ _ true, show promote (enters k) _= rankLevel q u from level_up _ _ _ false]; change promote B.BV (rankLevel q u) l+pairW V _ _ l=0
    rw [map_add,LinearMap.add_apply,Pi.add_apply,promised, lap_level B l, hv,show pairW V (rankLevel 2 L) _ l= _ from link_level B l hx hs,show pairW V (rankLevel 0 R) _ l= _ from link_level B l hE hs,hR,hu]; simp [rankLevel]
end Aura
end YM.MS.Native.Studio
