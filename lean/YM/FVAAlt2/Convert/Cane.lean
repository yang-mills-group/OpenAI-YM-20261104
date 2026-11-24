import YM.FVAAlt2.Convert.Fort
/-! Pre moment maps across horizons, BEFORE correction -/
noncomputable section
set_option autoImplicit false
namespace YM.FVAAlt2.Convert
open Finset Filter MeasureTheory Function Topology
open Labels Precision Extra.FD Maxwell Extraction FormalOPE FormalOPE.RG10
open PertExtension PertExtension.LatticePT PertExtension.Position
open FormalOPE.RG10.Position FormalOPE.RG10.Gazebo FormalOPE.RG10.Carryon
open MS MS.Koszul MS.Local.Physical MS.Menus MS.Book MS.Land
open PowerSeries (C coeff constantCoeff)
open Home Report Matrix Profiles
open scoped BigOperators Topology PowerSeries ContDiff Classical Matrix
variable {G:Gauge} {F:Frames G}{B:MS.Local.Physical.Deck G}
variable {U:MS.Land.Booked B}{d k n m:ℕ}(hk:d≤k)(μ:ℝ)(S:MS.Land.MS_Data G U)
local notation "V" n=> RG10.Position.Deck F n
local notation "K"=> ( Deck.climb F hk )
local notation "α"=> PertExtension.Physical.Profile.n
local notation "Ω"=> constantCoeff (R:=ℝ)
local notation:max "πA" j:max => ascend (PertExtension.Physical.Profile.n) j
local notation "G'"=> science μ S F
lemma current_l(p: Datum (Glyph B d)): currentM (B:=B) μ S ( πA (Home.up hk (B:=B)) p )= currentM μ S p:= rfl
lemma aboveList (i: V d)(j:Glyph B k)(he:j∉Set.range (Home.up (B:=B) hk)) : dout F B k (K i) j=0:= by
 apply Complex.ofReal_eq_zero.mp; rw [dout_at]; apply cite_b; intro H; have h: Deck.price F d i = j.size:= Eq.trans ( Eq.symm ( Deck.price_climb F hk i ) ) (congr_arg Prod.fst H); have ht:j.size≤d:= h ▸ Deck.price_bound F d i; exact he ( ⟨ ⟨ ⟨ j.size, Nat.lt_succ_of_le ht ⟩, j.2 ⟩ , show _= j from rfl⟩ )
lemma rootedOut(i: V d)(j:Glyph B d) : dout F B k (K i) (Home.up hk j)=dout F B d i j:= congr_arg Complex.re ( raised_b F B j i hk ) -- order
lemma scienceRise (p:Datum ( V d )): science μ S F k ( ascend α K p )= science μ S F d p:=by
 unfold science; obtain ⟨p,i⟩:=p; rw [ascend,monoread p (K ∘ i) _ _ (fun _=>Home.up hk (B:=B)) (fun _=> Home.up_inj _ ) ?_ ]; swap; · intro j i hi; rw [Function.comp_apply,Matrix.map_apply,aboveList hk _ _ hi,map_zero]
 unfold mix; apply sum_congr rfl; intro j _; refine congr_arg₂ (· * ·) rfl (prod_congr rfl fun z _=>?_); rw [Function.comp_apply,Matrix.map_apply,rootedOut hk]; rfl
variable (D:Stock F)
local notation "C1"=> Init G' D
def L0 (d:ℕ): Matrix (RG10.Position.Deck F d) (RG10.Position.Deck F d) (PowerSeries ℝ):= of ((D d).position (science μ S F d))
variable (hd:Official D)
include hd
lemma L_tied : clip K (L0 μ S D k)= L0 μ S D d:= by
 let g:=(G') d; let f:=(G') k; have hz : f ∘ πA K=g:= funext (scienceRise hk μ S)
 change clip K ((D k).position f)=(D d).position g; rw [← hz, (hd.tests d k hk).cast (Deck.climb_inj F hk) ]; rotate_left
 · have hq:Ω ∘ f=Gazebo.raw F k:= funext (physics F μ S); change (D k).Regular (Ω ∘ f); rw [hq]; exact hd.fresh k
 have h : Ω ∘ f ∘ πA K=Gazebo.raw F d:= hz.symm ▸ ( show Ω ∘ g=Gazebo.raw F d from funext (physics F μ S) ); change (D d).Regular (Ω ∘ f ∘ πA K); rw [h]; exact hd.fresh d
lemma L_foot : lowers K (L0 μ S D k):=(hd.tests _ _ hk).atCenter _
lemma L_0map : (L0 μ S D d).map Ω=1:= by
 rw [diag_one]; ext i j; simp only [ L0,Matrix.of_apply,Matrix.map_apply, Position.TestSystem.position_zero, hd.normal ]
lemma L_head : Stg (L0 μ S D d) 0=1:= by rw [← L_0map μ S D hd ]; ext i j; simp [Stg]
lemma L_tilt : Upright (L0 μ S D d):=by
 apply Upright.obtainable; rw [L_head μ S D hd,sub_self]; exact Submodule.zero_mem _
 intro i hi; rw [← agree hd]; exact (D d).positive_variation (G' d) i hi.ne'
-- substituted. exact f_T. This module doesn't assume H chosen lead.P.C.
variable (P:Plan F) {W:Booked (seats P.liftOff P.certified)}(X:MS_Data G W)(hp:Official P.stock)
local notation "z"=> Zpre P μ X
omit hd
include hp
lemma Z_0map : (z d).map Ω=(1: Matrix (V d) _ ℝ):= by unfold Zpre; rw [ ← L_0map μ X P.stock hp ]; ext i j; exact Warp.smoothed ..
lemma Z_head : Stg (z d) 0=1:= by rw [←Z_0map μ P X hp ]; ext i j; simp [Stg]
lemma Z_tied : clip K (z k)=z d:= funext fun i=>funext (fun j=>congr_arg (fun a:PowerSeries ℝ=> (f P μ X).charge a) (congr_fun (congr_fun ( L_tied hk μ X P.stock hp ) i) j))
lemma Z_foot : lowers K (z k):= by
 intro i j h; unfold Zpre; rw [Matrix.map_apply]; rw [show of ((P.stock k).position (science μ X F k)) (K i) j= 0 from L_foot hk μ X P.stock hp i j h,map_zero]
lemma Z_tilt : Upright (z d):= Warp.worth ( L0 μ X P.stock d ) _ ( L_tilt μ X P.stock hp )
end YM.FVAAlt2.Convert
