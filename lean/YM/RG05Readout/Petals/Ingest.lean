import YM.RG05Readout.Petals.Rain
import YM.RG05Readout.Bay.Audible
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Petals
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Cells Overlay
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons
open Records Basket Halls Shadow Flatten
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}
    {b k l:ℕ}{Q:ℝ}(h:C.Makes){D: Address.Rail C}{B:ℕ→ℕ→ℝ}
set_option quotPrecheck false
local notation "t!"=> (1,false)
local notation "L"=> C.path.levels
local notation "χ"=> C.path.levels.clock.J
local notation "λ₀"=> C.S.toDepth
local notation "Α"=> C.S.a
local notation "R0"=> C.path.rep N p
open Pulse Extraction Extraction.Lease
open Push.RelayDifference
variable {D:Address.Rail C}

local notation "L!"=> Lattice.wrap
variable {f: Extraction.Order}
/-!
# Manifest erasures under multi-charge. Price semantics additive.
 General vectors x only dollar (CAN grow) paid via normalization first in next file. Need actual valuation for residual discrepancy: witness is genuine Stencil bought on SAME extraction, not field projected by FREE. Supports price works before any normalization inside correlation tests. -/
open Dash Extraction Extraction.Lease UVExt -- Avoid `Slots` ambiguity namespace Petals.Slots
namespace Kernel
variable {F Z:Trial C}{v:Rowe C d}
noncomputable def times (s:Cutoffs→ℂ)(F:Trial C) : Trial C:= fun i j k=>s (i,j) • F i j k
lemma stenc_times (ht:Stencilled f F) (s:Cutoffs→ℂ): Stencilled f (times s F) := by
    obtain ⟨Z,hZ⟩:=ht; exact ⟨Z,hZ.mono (fun i hi=> hi.smul _)⟩

include h
omit h in
lemma implied {g:ℕ→ℕ→ℝ}(ht:Stencilled f F)(hx:rents F g f): CenterRents F (Function.uncurry g) f:=by
     refine ⟨ht.literal,fun j=>?_⟩; obtain ⟨k,hk,he⟩:= hx 1 j
     -- from UVExt/MixedRent.from_close
     refine ⟨k,hk,he.mono fun u hu=> hu.mono fun i hi=>?_⟩
     obtain ⟨hy,hF⟩:= hi; let T:= center C.S (f.per u) hy 0; exact ⟨hy,hF T rfl rfl 0 (Lease.fewer T 0 (Nat.div_le_div_left (by decide) (by decide)) (Stock.centered_margin ..))⟩
lemma close_minus (ht:Stencilled f F)(hz:Stencilled f Z)(hx:Bid.close C f F)(hy:Bid.close C f Z) : Bid.close C f (F-Z):=by
    obtain ⟨v₁,hp,hv⟩:= hx; obtain ⟨v₂,hq,hw⟩:= hy
    let w : Cutoffs→ℝ:= uncurry v₁+uncurry v₂; have hB: Tendsto w f.fuse (𝓝 0):= by have h:=hp.add hq; rw [zero_add] at h; exact h
    refine ⟨curry w,by rw [uncurry_curry]; exact hB,fun i k=> ⟨k,le_rfl,?_⟩⟩; let j:=8*(i+1); have hJ:0 < j:=by unfold j; omega
    have h0:=(implied ht hv).every h k j hJ; have h₁:=(implied hz hw).every h k j hJ
    unfold Order.late at *; filter_upwards [h0,h₁] with u hp hX; filter_upwards [hp,hX] with v ha hb
    obtain ⟨hl,hL⟩:=ha; obtain ⟨hk,hp⟩:=hb; refine ⟨hl,fun T hT _ x hx=>?_⟩; obtain ⟨ht,hK⟩:=hL T hT x hx; obtain ⟨hv,hg⟩:= hp T hT x hx
    let P:=F (f.mesh v) (f.per u) x; let Q':= Z (f.mesh v) (f.per u) x; have he: -Q'=(-1:ℂ) • Q':= neg_one_smul ℂ Q'|>.symm; let β:=C.beta (f.mesh v) (f.per u)
    change Interior _ (P-Q')∧ T.rootTest β (P-Q') ≤ w _; rw [sub_eq_add_neg,he]; exact ⟨ht.plus (hv.scale _), ((seamless h ..).semi T P _ ht (hv.scale _)).trans (add_le_add hK (by change T.rootTest β ((-1:ℂ) • Q') ≤ _; rw [Next.Extract.root_smul]; simp only [norm_neg,norm_one,one_mul]; exact hg))⟩ -- rhs
omit h in
lemma close_rotate (hx:Bid.close C f F)(s:Cutoffs→ℂ)(hz:∀ i, ‖s i‖≤1) : Bid.close C f (times s F):=by
   obtain ⟨q,hq,ha⟩:=hx
   refine ⟨q,hq,fun i j=>?_⟩; obtain ⟨k,hk,hv⟩:= ha i j; refine ⟨k,hk,hv.mono (fun i hi=> hi.mono fun v hv=> ?_)⟩; obtain ⟨hk,hV⟩:=hv
   exact ⟨hk,fun T hZ hT i' hi=> ⟨(hV T hZ hT i' hi).1.scale _, le_trans (by unfold times; rw [Next.Extract.root_smul];exact mul_le_of_le_one_left (T.root_nonneg ..) (hz _)) (hV T hZ hT i' hi).2⟩⟩ -- maybe

-- frames all eigen.Presentation of tested projection 
def Reveals (C:Family G)(f:Extraction.Order)(F:Trial C)(v:Rowe C d):Prop:= Stencilled f F∧ tight C f v∧ ∃ z:Trial C, UVExt.Slots.manifest z∧ Stencilled f z ∧ Bid.close C f (F-z-Bid.upper C v)
-- physical countdown. allowing ∃ z at ANY cycle. cost yields every seam.VAR.
lemma produce {S:YM.Table C.book}{R:Dash.Bin S}(hp:UVExt.Slots.StrongBin C R f d)
    (x: Rowe C d)(hc: dollar C f x)(ht:Stencilled f F)(hz:Bid.close C f (Bid.upper C x-F))(hv: tight C f (fun i=> (R d).step i (x i))): Reveals C f F (fun i=> (R d).step i (x i)):=by
    let v : Rowe C d:=fun i=> (R d).step i (x i); let V:= fun i=>x i-v i
    obtain ⟨z,hZ,hζ,hF⟩:= hp.mark V (fun i=>by simp only [V,v,map_sub,(R d).projection,sub_self]) (UVExt.dollar_sub hc (Work.D01.answer C h _ _ v hv))
    have hY := close_minus h ((Stencilled.upper h V).sub hζ) ((Stencilled.upper h x).sub ht) hF hz
    refine ⟨ht,hv,z,hZ,hζ,?_⟩; have h_V: Bid.upper C V= Bid.upper C x-Bid.upper C v:=funext fun n=>funext fun p=>funext fun w=> (C.linearO n p d w|>.mk' _).map_sub ..; rw [h_V] at hY
    convert hY using 1; abel
lemma faded (ht:Stencilled f F)(hx:Bid.close C f F): ∃ c:Cutoffs→ℝ, (∀ i,0<c i)∧ Tendsto c f.fuse (𝓝 0)∧ ∃ W:Trial C, F= times (fun i=>(↑(c i):ℂ)) W∧ Stencilled f W ∧ UVExt.Slots.TiledCaps C f W :=by
   obtain ⟨u,hU,hq⟩:=hx; let t:=flight C (-(1:ℝ)); let c(i:Cutoffs):= |u i.1 i.2|+t i
   have ht' (i):0 < c i:= add_pos_of_nonneg_of_pos (abs_nonneg _) (Real.exp_pos _); have hc:Tendsto c f.fuse (𝓝 0):= by have h := hU.abs.add (flight_lands (C:=C) one_pos); rw [abs_zero,add_zero] at h; exact h
   let s (i):ℂ:= (c i:ℂ)⁻¹; let W:= times s F; have ht(i):(↑(c i):ℂ)≠0:=Complex.ofReal_ne_zero.mpr (ht' i).ne'
   refine ⟨c,ht',hc,W,funext fun n=> funext fun p=> funext fun x=> ?_,stenc_times ‹Stencilled f F› s,?_⟩
   · dsimp only [W,times,s]; rw [smul_smul,mul_inv_cancel₀ (ht _),one_smul]
   apply UVExt.Slots.CenterCaps.offset ?_ h; intro j; obtain ⟨k,hk,hB⟩:=(implied ‹Stencilled f F› hq).billed j
   refine ⟨k,hk,1,zero_le_one,hB.mono (fun i hi=> hi.mono fun l hl=> ?_)⟩; obtain ⟨hp,hx,hZ⟩:=hl; let I : Cutoffs:= (f.mesh l, f.per i)
   refine ⟨hp,hx.scale _,?_⟩; unfold W times; rw [Next.Extract.root_smul]; change ‖s I‖*_ ≤1; rw [show ‖s I‖=(c I)⁻¹ by unfold s; rw [norm_inv,Complex.norm_real,Real.norm_of_nonneg (ht' I).le]]; rw [mul_comm, ←div_eq_mul_inv]; apply (div_le_one (ht' _)).mpr; exact hZ.trans ((le_abs_self _).trans (le_add_of_nonneg_right (show 0 ≤ t I from (Real.exp_pos _).le)))
end Kernel
end YM.RG05Readout.Petals
