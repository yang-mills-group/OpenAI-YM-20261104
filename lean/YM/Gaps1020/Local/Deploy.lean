import YM.Gaps1020.Local.Manifest
import YM.MergeProof.Tanger

set_option autoImplicit false
noncomputable section
namespace YM.GapsLocal.Full
open Function Filter Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Control Window Coat Footprint Raw Matter
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Stained Shield
open PhysicalNext PhysicalNext.Repeat Height Greenbelt
open Gas Ursell Trees RG.Supply Org Roost Opera
open Input Testing PriceCompiler
open AnalyticBridge VerifiedReset Collection Extra.Iteration Match Song Refrain Geo Quotes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat.Daisy.Charity.RG12
open YM.RG01.Survive
open YM.ConnectedActivityE6.Blaze.Thermal1020
open YM.ConnectedActivityE6.Blaze.Thermal1020.Shared
open UVExtension Spire Orchard Mast Oasis Progress.DirectedRecipe Mallow YM.RG12 OPE
open GridApprox.Nil Marker Merge MergeProof Accent
open YM.Overlay.GapsLocal
variable {G:Gauge}
open UVNext.CouplingReset
variable {hG:G.Simple} {X:Metals G}{D:Rolls X.p}{A:Alloy X D}{R:Factor A} {L:Side}{m n N ℓ j a b d k: ℕ}{l v:ℝ}
local notation "j0" => A.B.a.clock.J m
local notation "i0" => A.B.a.clock.J (m+1)
local notation "s0" => A.B.a.clock.hatBeta m
local notation "k0" => Real.sqrt (A.B.a.clock.forcedAllowance m)
local notation "k1" => Real.sqrt (A.B.a.clock.forcedAllowance (m+1))
local notation "S'" => A.B.a.clock.op m n
local notation "Z" => horizonRadius G (D.L i0) s0
set_option quotPrecheck false
variable {δ:Bid.Worth}{Q:ℕ→ℝ}{p:Legato.Bandage R Q δ} {t:ℕ→ℕ}(S:Spire.Uses R hG) (K:Cellar S t p)
local notation "X*" => Cellar.yard (roseA S) K
local notation "C0" => (X*).path.rep N n m
local notation "C1" => (X*).path.rep N n (m+1)
local notation "R!" => Pert.Asymptotics.regulatorRun (X*) N n (m+1)
variable (h:m<N)
local notation "E0" => (Orchard.ray S N n m (Orchard.rose0 S) h).body
local notation "z₀"=> Orchard.beam0
local notation "W0" => Mallow.houseS E0 z₀
local notation "β" => betaF G s0 (D.L i0)
section can
local notation "N'" => radiusB β
variable (he:Mallow.RG12.Earned (markerBudget G) R.shape A.delay)
include S K h he
lemma yardHeavy : 4*perStep i0 (C1).p.B ≤ Z^5:= by
   obtain ⟨h1,C,d,v0,Y,a',b',r',B,q',k',H,h'⟩:= Vacuum.Markets.certified W0 (R:=R) h he 0 (Nat.zero_le _); have hp:= h1.enough
   have hd: A.B.a.clock.hatBeta (m+1) = β:= Push.PriceCompiler.beta_eq A.B.valid m; have hB:1 ≤ β:= hd ▸ A.B.a.fits.delayed _ |>.le; have hZ:2 ≤ Z:=h'.large
   have hx':0<β:=by linarith
   let E:= perStep i0 N'; have hE:0 ≤ E:=by unfold E perStep Extra.Multi.siteFactor; positivity
   have hv:0 ≤ N':=Nat.zero_le _
   have hr: E*Mallow.probe β ≤ station β:= by
      let x:= radiusTab N' i0 (Mallow.probe β); have ht:=hp.buy; have hu:0<Mallow.probe β:=hp.probeT; let y:=Real.exp x*x; have hx:0≤ x:=by change 0≤ E*Mallow.probe β + 4*Mallow.probe β; positivity
      exact (le_add_of_nonneg_right (show 0≤4*Mallow.probe β from by positivity)).trans ((le_add_of_nonneg_right (show 0≤ y from by unfold y; positivity)).trans ht)
   unfold station Mallow.probe at hr; rw [Real.rpow_neg hx'.le, Real.rpow_neg hx'.le,Real.rpow_one, Real.rpow_two] at hr
   have hh : E ≤ Z^3:=by unfold horizonRadius; rw [←Real.rpow_mul_natCast hx'.le Thermal1020.ray]; apply le_trans (b:=β) ?_ ((Real.rpow_one β).symm.trans_le (Real.rpow_le_rpow_of_exponent_le hB (by norm_num [Thermal1020.ray]))); field_simp at hr; nlinarith
   have hv : (C1).p.B=N':= by
      rw [show (C1).p=A.B.a.budget (m+1) from ((E0).knows _ (z₀).property).1.point]; change radiusB _=N'; rw [← hd]
   rw [hv,show 5=2+3 by norm_num,pow_add]; exact mul_le_mul (by nlinarith) hh hE (by positivity)

omit S K h he in
private lemma glyph_limit : k1 ≤ 1:=by
   rw [Blush.glyph_eq]; unfold Blush.glyph; apply (Real.sqrt_le_iff).2; exact ⟨zero_le_one,(Real.exp_le_one_iff.mpr (by apply neg_nonpos.mpr; positivity)).trans_eq (one_pow _).symm⟩
variable {V:Type}[Fintype V] [DecidableEq V][Nonempty V]{E':Marker.Census V}(x: Overlay.Bands E' (S.realBeat (0:ℝ) N n (m+1)))(w:V→ℝ)
-- preserve every term in the source density, not replacing comparisons by
-- artifacts with re-assigned supports. Full valuation before any weak proxy;
-- temporary integer budget `a+5` read in B1 service. Remain denominator and
-- explicit normalization. Density here is in unnormalized Haar; normalization
-- for correlations represented with actual `eval` including hard masks.
def Targeted (a b d:ℕ)(e:ℝ) : Prop :=
    ∃ (I:Type)(_:Fintype I)(q:I→Menu.Hat E' (S.realBeat (0:ℝ) N n (m+1))),
      Overlay.GapsLocal.Shard (G:=G) (ι:=I) (R:=S.realBeat (0:ℝ) N n (m+1)) (n:=A.B.a.S.side (m+1) n) (B:=E') x q w (Z^(a+5)) ∧ Outfit (Q:=fun _=>S.realBeat (0:ℝ) N n (m+1)) E0 z₀ q w x.units x.origins (a+5) b d C0 e

lemma reach {C:ℝ} (hf:Service S K (n:=n) h (a+5) b j d C) (hx:∀ i:E'.Mode, i.val.card≤b)
    (hO: Extra.Multi.Occupancy ((A.B.a.clock.op m n).ratio.parent ∘ x.origins) i0)(hX:x.Active)(hR: x.Radial w l (Z^a) (Z^a) k1): Targeted S K (n:=n) h x w a b d l:=by
   have hV: HasSlots (C1).p (C1).activities:= Mast.slots1 S N m n (Orchard.rose0 S) h
   have he' := (W0).laws.intake.cap
   have hA : Menu.Arsenal C1:= Mallow.Many.sharp (A:=A) (m:=m) (n:=n) (Q:=fun _=>S.realBeat (0:ℝ) N n (m+1)) z₀ hV
   have hw: Extra.Multi.Occupancy x.origins i0:= fun i=> le_trans (by
      refine Finset.card_le_card ?_ ; intro a ha
      exact mem_filter.mpr ⟨mem_univ _, congr_arg _ (mem_filter.mp ha).2⟩) (hO ((S').ratio.parent i))
   obtain ⟨-,C,d',v0,Y,a',b',r',B,q',k',H,h'⟩:= Vacuum.Markets.certified W0 (R:=R) h he 0 (Nat.zero_le _)
   let H:= perStep i0 (C1).p.B; let z:= Z^a; have hr:= h'.large; have hH:0 ≤ H:=by unfold H perStep Extra.Multi.siteFactor; positivity
   have hz:0 ≤ z:=by unfold z; positivity
   have hp:2*(H*z)+2*(H*(z*k1)) ≤ Z^(a+5):=by rw [add_comm a,pow_add]; refine le_trans ?_ (mul_le_mul_of_nonneg_right (yardHeavy (n:=n) S K h he) hz); have he := mul_le_mul_of_nonneg_left (glyph_limit (A:=A) (m:=m)) (mul_nonneg hH hz); change 2*(H*z)+2*(H*(z*k1))≤4*H*z; nlinarith only [he]
   obtain ⟨I,u,q,hq⟩:= bait (D:=x) hX hR hw he'.labels hA hp
   exact ⟨I,u,q,hq,hf.covers _ hx x.origins w x.units q hO hq.price hR.pure hR.localU⟩
end can
end YM.GapsLocal.Full
