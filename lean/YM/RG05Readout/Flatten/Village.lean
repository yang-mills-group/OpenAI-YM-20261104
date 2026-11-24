import YM.RG05Readout.Flatten.Joints
import YM.UVExtension.Hearth.Palms
/-! Exact support windows for *all* terms on costed root array including clusters.
Used BEFORE invoking priced replication to sum a physical field. Doesn't
require extra support restriction on positions within each Native.box. License
depends on paid aperture b at J level and root geometry reach in n+1.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Flatten
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Cells Overlay
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station
open Records Basket Shadow
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}{I J V:Type}[DecidableEq V][Fintype V]
    {j b k D:ℕ}
set_option quotPrecheck false
local notation "t!"=> (1,false)
local notation "A"=> C.S.a
local notation "Λ"=> C.S.toDepth
local notation "X!"=> C.side N p
local notation "Y!"=> C.side b p
local notation "s!"=> n+1
local notation "P"=> C.side (n+1) p
open GridApprox
section loci
variable (h:C.Makes)
abbrev Scope (C:Family G)(d:ℕ):= (Finset.range (d+1)).sup (fun e => stencilRadius C e)
local notation "ℓ₀"=> Scope C D
include h
lemma flower (v:Palette C d)(x:Site X!)(q:Body) (hp:d ≤ D): Interior (window x ℓ₀) (stepUp t! x (entrance C d N p v 0 q)):=by
    have ht: Interior (window 0 ℓ₀) (entrance C d N p v 0 q):=by
       unfold entrance; apply YM.UVExtension.Hearth.inSum; intro i _; let T:=C.localSection (kept i.1); let F:=C.labels.level (kept i.1); apply Interior.scale; apply Interior.scale; unfold presented
       let u:= F.scaled (C.path.rep N p N).p.threshold⁻¹ (Size.axis F i.2); change Interior _ (T.places u 0); have hh:=T.continuous_places (n:=X!) u 0
       have hV: Interior (T.footprint (0:Site X!)) (T.places u 0):=⟨T.placed_invariant (h.sections _) 0 u,hh.measurable,T.placed_local 0 u,(Envelope.compactC hh).cost⟩
       exact hV.enlarges ((stencil_fits C (kept i.fst) 0).trans (YM.UVExtension.Hearth.window_large (Finset.le_sup (f:=fun i=>stencilRadius C i) (mem_range.mpr (lt_of_le_of_lt ((Nat.sub_le ..).trans hp) (Nat.lt_succ_self _))))))
    have hk:= translated_window x ht
    unfold stepUp; simp_rw [pull_one, Motion.scalar]
    rw [zero_add] at hk; exact hk
omit h in
lemma window_of_le {n:Side}(x o:Site n)(r:ℕ)(hx:separation x o ≤ r): x∈ window o r:=by
     let u:= x-o; have hk : lift u ∈ Lattice.box r:=by
         rw [box_test]; unfold separation at hx; constructor <;> intro i <;> have := (component_le u i).trans hx <;> omega
     exact ⟨lift u,hk, (add_left_inj o).mpr (wrap_lift u)|>.trans (sub_add_cancel x o)⟩
variable (hr:j ≤ b)(hb:b ≤ n+1)(ht:n+1 ≤ N)
local notation "u"=> Λ hr p
local notation "c"=> Λ hb p
local notation "d'"=> Λ ht p
local notation "hl"=> (hr.trans hb).trans ht
local notation "w₀"=> (Λ hl p).count.val
local notation "C₀"=> u|>.count.val
local notation "C₁"=> c|>.count.val
local notation "C₂"=> d'|>.count.val
local notation "W"=> tilesAt C.S p hl
variable {g:ℕ} (z:Site (C.side b p))(hf:separation z 0 ≤ (C.S.toDepth hr p).count.val/4)(hx: 16*(1+g+Scope C D) ≤ (C.S.toDepth hr p).count.val)
include z hf hx
omit h in
lemma payInside (y:Site P) (hy:(c).parent y=z)(x:Site P)(hp:separation x y ≤ g)(s:Site X!)(he:(d').parent s=x) : window s ℓ₀⊆ (W).chamber 0:=by
    let K:=(Λ hl p); have h_κ(w)(hw:w∈window s ℓ₀):2*separation w (anchor C.S p hl 0) < (K).count.val:=by
       rw [show anchor C.S p hl 0=0 from map_zero (K).root]; have h₁:=midway (d') (C.S.toDepth_odd ht p) s; rw [he] at h₁; have h₂:=midway (c) (C.S.toDepth_odd hb p) y; rw [hy] at h₂
       let l:= separation w s; let L:=(d'); let t:= (c).embed z; have hl' : separation w s≤ ℓ₀:=by
           obtain ⟨T,hT,rfl⟩:=hw; rw [separation_comm]; exact Work.E08.separation_box_add s hT
       have h₃:= separation_triangle x y t; have h₄:=separation_triangle w s (L.embed x); have h₅:= separation_triangle w (L.embed x) (L.embed t); rw [both L] at h₅
       have h₆: separation w 0 ≤ separation w (L.embed t)+C₂*(C₁*separation z 0):= by
           have h: separation (L.embed t) (L.embed ((c).embed 0)) = C₂*(C₁*separation z 0):= by unfold t; rw [both L,both];
           rw [show (c).embed 0=0 from (c).root.map_zero,show L.embed 0=0 from L.root.map_zero] at h; exact le_trans (separation_triangle w (L.embed t) 0) (Nat.add_le_add_left h.le _)
       have h₈: 2*separation x t ≤ 2*g+C₁:=by linarith only [hp,h₃, show 2*separation y t < C₁ from h₂]
       have h₇: 2*separation w 0 ≤ 2*ℓ₀+C₂*(1+2*g+C₁+C₁*(2*separation z 0)):= by
          linarith only [h₄,h₅,h₆,h₁,hl',Nat.mul_le_mul_left C₂ h₈]
       rw [size_comp (Λ (hr.trans hb) p) L K,size_comp (u) (c)]; refine h₇.trans_lt (lt_of_le_of_lt ?_ (Nat.mul_lt_mul_of_pos_left (show 1*(1+2*ℓ₀+2*g)+C₁+C₁*(2*separation z 0)< C₁*C₀ from ?_) (L.count.property: 0<C₂)))
       swap
       · have ht₁: 2+2*ℓ₀+2*g≤ C₁*(2+2*ℓ₀+2*g):= Nat.le_mul_of_pos_left _ ((c).count.property:0<C₁)
         have htP : (2+2*ℓ₀+2*g)+1+ 2*separation z 0 < C₀:=by omega
         have hi: _<C₁*C₀:=Nat.mul_lt_mul_of_pos_left htP ((c).count.property:0<C₁); simp_rw [Nat.mul_add] at hi ht₁; omega
       linarith only [show 2*ℓ₀ ≤ C₂*(2*ℓ₀) from Nat.le_mul_of_pos_left _ L.count.property]
    rw [GridApprox.tiling_window]
    intro w h₀; have H:= h_κ w h₀; exact window_of_le _ _ _ (by change separation w (anchor C.S p hl 0) ≤ K.count.val/2;omega) -- edit
lemma clusterInside (y:Site P)(hy:(c).parent y=z)(x:Site P)(hp: separation x y ≤ g)(hd: d ≤ D)(v:Palette C d)(f:Body): Interior ((W).chamber 0) (clinic C p N d v s! x t! f):=by
    rw [Records.clinic,lift_pol (le_refl N) (precinct C p N d v) ht]; refine YM.UVExtension.Hearth.inSum _ _ _ (fun i _=> ?_); rw [Records.like_embed]; let t:=(d').assemble (x,i); exact ((flower h v t (feeR (d') i f) hd).enlarges (payInside hr hb ht z hf hx y hy x hp t ((d').assemble_parent _))).scale _
omit h z hf hx in
private lemma around (y:Site P) (x:Site P)(v:Palette C d)(f:Body): stepUp t! ((d').embed y) (clinic C p N d v s! x t! f)=clinic C p N d v s! (x+y) t! f:=by
   unfold clinic uniform; rw [dif_pos ht,dif_pos ht,shiftE]; exact congr_arg (fun z=>stepUp t! z _) ((map_add (d').root x y).symm)
omit h z hf hx in
private lemma planD {f:Side}{F:I→Goods G f}(x:Site f)(s:Finset I): stepUp t! x (fun U=>∏ i∈s,F i U)=fun U=> ∏ i∈s,stepUp t! x (F i) U:=rfl
-- uses every growth census
omit [DecidableEq V] in
lemma plotIn (R:V→Site P)(H: V→ℕ)(F:V→Body)(s:(j:V)→ Palette C (H j))(T:PulseC)(v : Palette C d)(q:Body)(hd: d ≤ D)(hV:∀ i,H i ≤D)(hP:∀ i,separation (R i) 0 ≤ g) :
     let X:= bunchG (C:=C) (N:=N) R H F s
     Interior ((W).chamber 0) (uniform C s! p N d ht (rebirth C d n p N ht T v X) b z (1,false) q):=by
     intro X; rw [lift_pol ht (rebirth C d n p N ht T v X) hb]; refine YM.UVExtension.Hearth.inSum _ _ _ (fun i _=> ?_); unfold rebirth; rw [Records.rot_sub, Records.rot_scalar]; let y:=(c).assemble (z,i); have hy:(c).parent y=z:= (c).assemble_parent _; let Y':=stepUp t! ((d').embed y) X; have hY: Interior ((W).chamber 0) Y':=by
         unfold Y' X bunchG; rw [planD]; refine Interior.combines _ _ (fun a _=>?_); rw [around ht]; exact clusterInside h hr hb ht z hf hx y hy _ (by have hlP:=hP a; apply le_trans (le_of_eq ?_) hlP; unfold separation; rw [add_sub_cancel_right,sub_zero]) (hV a) _ _
     let f' := feeR (c) i q; have he: stepUp t! ((d').embed y) (crops C N p N d le_rfl (precinct C p N d v) s! ht f') = clinic C p N d v s! y t! f':=by unfold clinic uniform;rw [dif_pos ht]
     exact (Next.UVStress.minus (Y:=Motion.scalar t! _ • Y')  (hY.scale _) (he.symm ▸ clusterInside h hr hb ht z hf hx y hy y (by simp) hd v f')).scale _ -- edit
end loci
end YM.RG05Readout.Flatten
