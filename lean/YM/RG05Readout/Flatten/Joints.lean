import YM.RG05Readout.Halls.Siren
/-!
# Flatten the nested odd address charts of Records at actual cutoff.
No quotienting offsets in Dyn even though torus chart for site reps can wrap.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Flatten
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion Cells
open Overlay Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons Ribbons.ManyCopies
open Records Basket Shadow
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G}
set_option quotPrecheck false
section ratios
variable {n c f:Side}(a:Ratio n c)(b:Ratio c f)(r:Ratio n f)
local notation "Θ"=> Lattice.wrap
-- relative native cells.Code
noncomputable def chain (a:Ratio n c)(b:Ratio c f)(r:Ratio n f)(x:Site a.count × Site b.count): Site r.count:= Θ r.count (b.count.val • lift x.fst+ lift x.snd)
local notation "k"=> chain a b r
local notation "L"=> (a.count.val)
local notation "K"=> (b.count.val)
lemma chain_lift (ha:Odd a.count.val) (hb: Odd b.count.val)(x:Site a.count × Site b.count): lift (k x)= K • lift x.1 + lift x.2:=by
    rw [lift_eq_iff]; refine ⟨rfl,fun i=>?_⟩
    rw [size_comp a b r]; change -(↑(K*L):ℤ)<2*(K • lift x.fst i+ lift x.snd i) ∧ 2*(K • lift x.fst i+ lift x.snd i)≤ ↑(K*L)
    rw [nsmul_eq_mul]; let u:= lift x.1 i; let v:=lift x.2 i
    have h₁: -(L:ℤ)+1≤2*u:=Int.add_one_le_of_lt (lift_centers x.1 i).1
    have h₂: -(K:ℤ)<2*v:=(lift_centers x.2 i).1
    have r₁: 2*u+1≤ (L:ℤ):=Int.add_one_le_of_lt (Ratio.unambiguous ha x.1 i)
    have r₂: 2*v<(K:ℤ):=Ratio.unambiguous hb x.2 i
    push_cast; have hk:0<(K:ℤ):=Int.natCast_pos.mpr b.count.property
    change -(↑K*↑L:ℤ) < 2*((K:ℤ)*u+v) ∧ 2*((K:ℤ)*u+v) ≤ (K:ℤ)*L; constructor
    · linarith only [mul_le_mul_of_nonneg_left h₁ hk.le,h₂]
    linarith only [mul_le_mul_of_nonneg_left r₁ hk.le,r₂]
lemma chain_assembly (ha:Odd a.count.val)(hb:Odd b.count.val)(x:Site a.count × Site b.count)(z:Site n) : r.assemble (z,k x)=b.assemble (a.assemble (z,x.1),x.2) :=by
   unfold Ratio.assemble; dsimp only; rw [chain_lift _ _ _ ha hb,map_add,embed_comp a b r,show b.embed (_+_)=_ from b.root.map_add ..,Ratio.root_embed,Ratio.root_embed,b.embed_wrap,add_assoc]
noncomputable def appendR (ha:Odd a.count.val)(hb:Odd b.count.val): Site a.count × Site b.count ≃ Site r.count:= Equiv.ofBijective k (by
    apply (Fintype.bijective_iff_injective_and_card _).mpr; refine ⟨?_,?_⟩
    · intro x y h; let s:= fun i:Site r.count=>r.assemble (0,i)
      have hp:= congr_arg s h; unfold s at hp; rw [chain_assembly _ _ _ ha hb,chain_assembly _ _ _ ha hb] at hp; let v:= b.assemble_bijective.1 hp; exact Prod.ext (congr_arg Prod.snd (a.assemble_bijective.1 (congr_arg Prod.fst v))) (by have hh:=congr_arg Prod.snd v; exact hh)
    rw [Fintype.card_prod,site_card,site_card,site_card,size_comp a b r,mul_pow,mul_comm])
noncomputable def placeR (r:Ratio n f)(x:Site r.count):E4:=((r.count.val:ℝ)⁻¹) • WithLp.toLp 2 (fun i => (lift x i:ℝ))
lemma originR (r:Ratio n f): placeR r 0=0:=by simp [placeR]; rfl
noncomputable def feeR (r:Ratio n f)(x:Site r.count):Body →ₗ[ℂ] Body:=Native.pull (placeR r x) ((r.count.val:ℝ)⁻¹)
lemma fineE (ha:Odd a.count.val)(hb:Odd b.count.val)(x:Site a.count × Site b.count)(y:E4): placeR a x.1+((a.count.val:ℝ)⁻¹) • (placeR b x.2+((b.count.val:ℝ)⁻¹) • y)= placeR r (k x)+((r.count.val:ℝ)⁻¹) • y:=by
   unfold placeR; rw [chain_lift a b r ha hb]; rw [size_comp a b r]; push_cast
   apply PiLp.ext; intro i
   change ((L:ℝ)⁻¹) * (lift x.1 i:ℝ) + ((L:ℝ)⁻¹)*(((K:ℝ)⁻¹)*(lift x.2 i:ℝ)+((K:ℝ)⁻¹)*y i)= ((K:ℝ)*(L:ℝ))⁻¹*((K • (lift x.1 i) + lift x.2 i:ℤ):ℝ) + ((K:ℝ)*(L:ℝ))⁻¹*y i
   rw [nsmul_eq_mul]; push_cast; field_simp; ring
lemma fee_chain (ha:Odd a.count.val)(hb:Odd b.count.val)(x:Site a.count × Site b.count)(p:Body):feeR r (k x) p=feeR b x.2 (feeR a x.1 p):= Subtype.ext (funext fun y=> congr_arg p.val (fineE _ _ _ ha hb x y).symm)
lemma mapsR (r:Ratio n f)(h:Odd r.count.val)(y:Site r.count): MapsTo (fun x:E4=> placeR r y +((r.count.val:ℝ)⁻¹) • x) Native.box Native.box:=by
    intro x hx i; have he :0 < (r.count.val:ℝ):=by exact_mod_cast r.count.property
    have hp:= abs_le.mp (hx i)
    have hv: -(r.count.val:ℝ)+1≤2*(lift y i:ℝ):=by exact_mod_cast Int.add_one_le_of_lt (lift_centers y i).1
    have hv': 2*(lift y i:ℝ)+1 ≤ (r.count.val:ℝ):=by exact_mod_cast Int.add_one_le_of_lt (Ratio.unambiguous h y i)
    let T:ℝ:=r.count.val; change |T⁻¹*(lift y i:ℝ)+T⁻¹*x i| ≤ 1/2
    rw [← mul_add, mul_comm (T⁻¹),←div_eq_mul_inv]; apply abs_le.mpr; unfold T; rw [div_le_iff₀ he, le_div_iff₀ he]; constructor <;> linarith
-- exact dimensions are fixed 4
abbrev ratioX (r:Ratio n f)(d:ℕ) :ℂ:= (( (r.count.val:ℝ)^d/(r.count.val:ℝ)^4:ℝ):ℂ)
lemma ratioX_mul (d:ℕ): ratioX a d* ratioX b d= ratioX r d:=by unfold ratioX; rw [size_comp a b r]; push_cast; rw [mul_pow,mul_pow]; ring
end ratios

section capture
variable {i n m p N d:ℕ}{n':Side}
local notation "Z!"=>C.S
local notation "t!"=> (1,false)
local notation "Λ"=> C.S.toDepth
local notation "χ"=>C.path.levels.clock.op
lemma shiftE (x y:Site n') (f : Goods G n') : stepUp t! x (stepUp t! y f)= stepUp t! (y+x) f:=by
    rw [View.step_cycle]; simp [MergeProof.twist,affine]
local notation "Γ"=> fun y f=>stepUp t! y f
lemma chain_price (d:ℕ): budwgt C p i d=ratioX (χ i p).ratio d :=by unfold budwgt ratioX; simp; rfl
variable (hm:m ≤ N) (L:Bin G (C.side N p))
local notation "c!"=> crops C m p N d hm L
lemma ratio_one (a:Ratio n' n'): a.count.val=1:= Nat.eq_of_mul_eq_mul_left n'.property (a.exact_size.symm.trans (Nat.mul_one _).symm)
lemma awaken (f:Body) (hi:i ≤ m) : let r:=(Λ hi p)
        c! i hi f = ∑ y:Site r.count, ratioX r d • Γ ((Λ hm p).embed (r.assemble (0,y))) (L (feeR r y f)):=by
   intro r; induction hi using Nat.decreasingInduction generalizing f with
   | self=> rw [crops_head _ hm]; have ht:= ratio_one r; have he(t:Site r.count):t=0:= Fintype.card_le_one_iff.mp (by rw [site_card,ht,one_pow]) t 0
            rw [sum_eq_single 0]; rotate_left
            · intro t _ h; exact (h (he t)).elim
            · simp
            have hp: feeR r 0 f=f:=by apply Subtype.ext; funext y; change f.val (placeR r 0+((r.count.val:ℝ)⁻¹) • y)=_;rw [originR,ht];simp
            have hΩ: ((Λ hm p).embed (r.assemble (0,0)))=0:=by rw [Ratio.assemble, show r.embed 0=0 from r.root.map_zero]; simp; exact (Λ hm p).root.map_zero
            unfold ratioX; rw [hΩ,hp,ht]; simp [stepid]
   | of_succ i hi ih=>
        let a:=(χ i p).ratio; let b:=(Λ hi p); let u:= r; let s:= (Λ hm p); let h₁:Odd a.count.val:=C.S.block_odd i; let h₂:= C.S.toDepth_odd hi p
        rw [crops_step _ hm hi]; unfold replenishes Bud
        rw [← Equiv.sum_comp (appendR a b u h₁ h₂),Fintype.sum_prod_type]; refine sum_congr rfl fun x _=> ?_; rw [ih _,Records.rot_sum,smul_sum]
        refine sum_congr rfl fun y _=> ?_; rw [Records.rot_scalar]; let P:= feeR a x f; change budwgt C p i d • (ratioX b d • stepUp t! _ (stepUp t! _ (L (feeR b y P))))= ratioX u d • stepUp t! (s.embed (u.assemble (0,chain a b u (x,y)))) (L (feeR u (chain a b u (x,y)) f)); rw [smul_smul,chain_price,ratioX_mul a b u d, chain_assembly _ _ _ h₁ h₂,fee_chain _ _ _ h₁ h₂,shiftE]; congr 2; rw [embed_comp b s]; let z:= a.assemble (0,x); change s.embed (b.assemble (0,y))+s.embed (b.embed z)=s.embed (b.assemble (z,y)); rw [← show s.root _=s.embed (b.assemble (0,y)) from rfl,← show s.root _=s.embed (b.embed z) from rfl,←s.root.map_add]; unfold Ratio.assemble; rw [show b.embed 0=0 from b.root.map_zero,zero_add,add_comm]; rfl
lemma lift_pol (ht:i ≤ m)(z:Site (C.side i p))(f:Body): let r:=(Λ ht p)
        uniform C m p N d hm L i z (1,false) f = ∑ y:Site r.count, ratioX r d • stepUp t! ((Λ hm p).embed (r.assemble (z,y))) (L (feeR r y f)):=by
    intro r; unfold uniform; rw [dif_pos ht,awaken,Records.rot_sum]; refine sum_congr rfl (fun y _=> ?_);rw [Records.rot_scalar, shiftE,embed_comp r (Λ hm p)]
    let s:= (Λ hm p); change ratioX r d • stepUp t! (s.embed (r.assemble (0,y))+s.embed (r.embed z)) _=_; rw [← show s.root (r.assemble (0,y))=_ from s.root_embed _, ← show s.root (r.embed z)=_ from s.root_embed _,← map_add]; unfold Ratio.assemble; rw [show r.embed 0=0 from r.root.map_zero,zero_add,add_comm]; rfl
end capture
end YM.RG05Readout.Flatten
