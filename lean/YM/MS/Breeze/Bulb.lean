import YM.MS.Breeze.North
import YangMills.WilsonProof.NativeSupport.YM.MS.Puff.State
/-! Price at each scale for gluing/Wick.S.Submodule -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Breeze
open Garment.Wick
open Set Function Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native
open Lattice City Latch Job Belt Flux Wire Book Convolve Orbit Puff Rake Rake.Geo
open scoped Topology ContDiff Interval
variable {I E:Type} {G:Gauge}{F H:Law G}{t:ℝ}
local notation "Ψ"=> (field (p:=Landau.parity ( A:=Axis ) (C:=G.ColorIndex) ) (P:=QP))
local notation "K"=> (Job.single Unit)
local infix:70 " ⋄ "=> product (field Landau.parity)
abbrev deep (G:Gauge)(s:ℝ):= orbit ( PlanetD G s ) planeF
lemma weightC (hp:F∈ Wallet G)(s:ℝ): deep G s F=Ccy ( PlanetD G s ) F planeF:= finite_cc planeF (Wallet.cour hp _)
def Roof (G:Gauge):= Wallet G⊓ Center ( field ( P:=QP ) ( Landau.parity ( A:=Axis ) ( C:=G.ColorIndex ) ) )
lemma thClosed (s:ℝ): closed (PlanetD G s) Landau.parity false:= cl_a G s 0
lemma thRev (s:ℝ): Reverse (PlanetD G s) Landau.parity:= reverse_a G s 0
lemma Roof.core (hp:F∈Roof G)(ht:H∈ Roof G): F ⋄ H∈ Roof G:= ⟨ Wallet.product hp.1 ht.1,Pure.prod (b:=false) (c:=false) hp.2 ht.2 ⟩ -- binder
lemma Roof.unit : (coin (1:ℂ))∈ Roof G:= ⟨ Wallet.cash, coin_pure 1 ⟩
lemma Roof.deep (hp:F∈ Roof G)(s:ℝ): ( Breeze.deep G s F )∈ Roof G:= by
    rw [ weightC hp.1 ]; refine ⟨ Wallet.skyC hp.1 _,?_⟩; intro l hv; change (∫ p,trc (PlanetD G s) p F l∂planeF)=0; suffices he : ∀ p:QP,trc ( PlanetD G s ) p F l=0 by simp_rw [he]; simp
    intro p; rw [ at_trc ]; refine Finset.sum_eq_zero fun i _=> Finset.sum_eq_zero fun j _=>?_ ; by_cases he : PlanetD G s i j p=0; rw [he,zero_mul]; obtain ht:= thClosed s i j p he; rw [hp.2 ( (i,p)::(j,-p)::l ) (show (parity i ^^ (parity j ^^ degree Ψ l))≠ false from (by rw [ ← Bool.xor_assoc,Bool.xor_comm (parity i),ht,Bool.false_xor ]; exact hv) ),mul_zero] -- p implicit
abbrev linkD (G: Gauge)(s:ℝ):= tokenL (deep G s) false ( field Landau.parity )
abbrev touchD (G:Gauge)(s:ℝ)(p:QP):= tokenL (trc (PlanetD G s) p) false (field Landau.parity)
lemma choirD (p:QP)(s:ℝ)(A:Law G)(hx:F∈Roof G)(hp:H∈Roof G)(hu:A∈Roof G): touchD G s p F ( H ⋄ A )= touchD G s p F H ⋄ A+ H ⋄ touchD G s p F A:= by
    change link _ _ _ _ _=(link _ _ _ _ _ ⋄ A)+ H ⋄ link _ _ _ _ _; unfold trc; simp_rw [ link_sum,link_scale,map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply,← Finset.sum_add_distrib ]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>?_ ; by_cases he: PlanetD G s i j p=0; simp [he]; rw [ pair_products (p:=Ψ) (i,p) (j,-p) ( show (parity j ^^ parity i)=false from thClosed s i j p he ) hx.2 hp.2, smul_add ] -- Rhythm
lemma buyer (H:Law G): Sensible ( fun F=> F ⋄ H ):= by refine ⟨fun i=>?_⟩; simp_rw [scattered]; apply cent_gather (field Landau.parity) i _; intro k l hl; simp_rw [ mul_comm (_:ℂ) ( H l ) ]; apply cent_scale _ _ ( centroid _ ) -- guess
lemma seller (H:Law G): Sensible (fun F=> H ⋄ F):= by refine ⟨fun i=>?_⟩; simp_rw [scattered]; exact cent_gather (field Landau.parity) i _ (fun a b _=> cent_scale _ _ ( centroid _ ) )
lemma gateway (hf:F∈ Wallet G)(hp:H∈ Wallet G)(s:ℝ)(w:Legs (Lane4 G)): Integrable (fun p=> touchD G s p F H w) planeF ∧ linkD G s F H w=∫ p,touchD G s p F H w∂planeF:= by
    let L:= PlanetD G s; obtain ⟨h₁,h₂⟩:= cycle_map planeF _ (buyer H) w (Wallet.cour hf s); obtain ⟨h₃,h₄⟩:= cycle_map planeF _ (seller F) w ( Wallet.cour hp s ); obtain h₅:= Wallet.cour ( Wallet.product hf hp ) s w; simp only [tokenL,touchD,linkD,LinearMap.coe_mk,AddHom.coe_mk,link,sign_id,Pi.sub_apply]; rw [ weightC ( Wallet.product hf hp ), weightC hf,weightC hp ]; exact ⟨ (h₅.sub h₁).sub h₃, (by rw [ show (∫ p:QP,trc (PlanetD G s) p (F ⋄ H) w- (trc (PlanetD G s) p F ⋄ H) w-( F ⋄ trc (PlanetD G s) p H ) w∂planeF)= (∫ p:QP,trc (PlanetD G s) p (F ⋄ H) w-(trc (PlanetD G s) p F ⋄ H) w∂planeF)-(∫ p:QP,( F ⋄ trc (PlanetD G s) p H ) w ∂planeF) from integral_sub ( h₅.sub h₁ ) h₃, integral_sub h₅ h₁,h₂,h₄ ])⟩ -- syntax
lemma whisperD (R:Law G)(hf:F∈Roof G)(hp:H∈Roof G)(ht:R∈Roof G)(s:ℝ): linkD G s F (H ⋄ R)= linkD G s F H ⋄ R+ H ⋄ linkD G s F R:= by
    have he(w):= gateway hf.1 hp.1 s w; have hv(w):=gateway hf.1 ht.1 s w; have hz : linkD G s F H=(fun w=>∫ p,touchD G s p F H w∂planeF):= funext fun w=>(he w).2; have hh : linkD G s F R=(fun w=>∫ p,touchD G s p F R w∂planeF):= funext fun w=>(hv w).2;
    funext w; obtain ⟨hA,hB⟩:=cent_arguments planeF ( ( buyer R ).reaches w ) (fun l=>(he l).1); obtain ⟨ht',hq⟩:= cent_arguments planeF ((seller H).reaches w) (fun i=> (hv i).1 ); rw [( gateway hf.1 ( Wallet.product hp.1 ht.1 ) s w ).2 ]; simp_rw [choirD _ _ R hf hp ht,Pi.add_apply, integral_add hA ht',hz,hh ]; exact congr_arg₂ ( · + · ) hB hq -- simp_rw hA unif fails
variable (G)
def Shine : Actors (Law G):={ ( actor (field Landau.parity) ) with
   guard:= Roof G
   holds:= Roof.unit
   close:= fun _ h _ hv=> Roof.core h hv
   turns:= fun _ hx x _=> Pure.central hx.2 x }
lemma ω0 (s:ℝ): deep G s ( Shine G ).unit=0:= by rw [ weightC ( show ( Shine G ).unit∈ Wallet G from Wallet.cash ) ]; ext; unfold Ccy; simp [Shine,actor,coin] -- ξ
-- use @t focal.
def Move (s:ℝ): Puff.Engine ( Shine G ) where
   move:=deep G s
   unitLaw:=ω0 G s
   join:= linkD G s
   stays:= fun _ h=> Roof.deep h s
   compatibility F H hX _:= by change deep G s ( F ⋄ H )=( deep G s F ⋄ H )+(F ⋄ deep G s H )+link ( deep G s ) false _ _ _; rw [link_even (b:=false) _ hX.2]; abel
   leib F H R hx hy hR:= whisperD R hx hy hR s
end YM.MS.Breeze
