import YM.RGComparison01.Marks.Ink
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Pledge
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter Mixed Reserves
open PhysicalNext PhysicalNext.Repeat Packets Art Silica Poll Pond Shield Eider Gas Ursell Trees Height Sail
open PhysicalNext.Repeat.Lotus Team Merge
open AnalyticBridge VerifiedReset Collection Quotes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge} {ι : Type} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {R : RG.Rep G f}
    {n : ℕ} {W a r σ Λ μ s κ w c' C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
    {H : Cash W s μ L Q o C T R} {d C' A B e δ t D D' v K :ℝ} {j k ℓ:ℕ} {χ:Chi} {Ω : Utopia H j v d r C' χ}
    {Ψ : ℕ → Prop} {x:ℕ→ℝ}
namespace Heron
open Foreman Checks Baked Palette Pillow Resin Season Ink
open Switch Mallow Ovens OmitClusters PhysicalNext.Repeat.Song
variable [Fintype ι]
variable (M:ι→Leaf R)(g:ι→ℝ) (H:Cash W s μ L Q o C T R)(Γ:Match.Alliance H H 1 0)(V:Config G c)(F : Tree.Forest S.ratio)
local notation "Pt"=> Q.mark L μ s
local notation "CL"=> Cl M H
local notation "CM"=> Cake M H
local notation "go" => Palette.ways g
variable (P':BudgetPoint)(hB:P'.B=radiusB s)(hp:P'.threshold=Pressure.temp s)(hq : Ringlet H M g a δ A B)
include hp hq
variable (h : Rooted (origins M H) (fun p=> Pillow.glass M g χ p) P' a e)
  (he:∀ p:Cl M H,Pillow.pottery M g χ p= masked P'.threshold (origins M H p) (Pillow.glass M g χ p))
local notation "G'" => Ink.yielded M g H (χ:=χ)
include h he hB
lemma tally : ∃ b:Cl M H→ℝ,(∀ i,Paid (fun U=>Ink.paths M g H i U (χ:=χ)) (b i) ∧ Paid ((G') i) (b i))∧ Ac.Hit (origins M H) P'.B b a e ∧ Summable b:= by
   obtain ⟨b,hv,hF⟩:=h; refine ⟨b,fun i=>?_,hF,Daisy.Charity.everyoneN (origins M H) _ (fun i=> (hv i).2.1) (show Ac.Hit (origins M H) (radiusB s) b a e from hB ▸ hF) (fun p _=> Finset.Nonempty.mono (subset_biUnion_of_mem (raised M H ∘ p.2) (Finset.mem_univ none)) (p.2 none).1.2.1) hq.value⟩
   have hh:= backed M g H (χ:=χ) i P' hp (b:=b i) (hv i).2.2 (he i); refine ⟨hh,?_⟩; by_cases hf :Season.allot i=0; swap
   · have hx : (G') i= Ink.paths M g H (χ:=χ) i:= funext fun V=> funext fun x=> funext fun z=> if_pos hf; rw [hx]; exact hh
   rw [show (G') i= (0:Config G c →Ways ι) from funext fun U=>funext fun x=>funext fun z=> if_neg (not_not.mpr hf)]; exact paidZero.weaken (hv i).2.1

def bouquet (x:ℝ)(q:Finset ι) := ∑' i:Cl M H,yielded M g H (χ:=χ) i V x q
local notation "Xq" => Greenbelt.prism T s χ o.K V F
local notation "V0" => overhead Xq R Q.table

include F
lemma life (i : ℝ)(hi:i∈Set.Icc (0:ℝ) 1)(p:Finset ι) : Real.exp (bouquet M g H V i p (χ:=χ))*H.homesteadPool χ V= H.homesteadMill (Palette.color M H χ V (Palette.ways g i p)):= by
   let Fp i v:= H.homesteadMill (Palette.color M H χ V (Palette.ways g i v)); let P : Ways ι:= fun x v=> ∑' z:CL, paths M g H (χ:=χ) z V x v
   obtain ⟨b,ht,hb,hS⟩:= tally M g H P' hB hp hq h he; have hsum i (hi:i∈Set.Icc (0:ℝ) 1) v: Summable fun p=> paths M g H (χ:=χ) p V i v:= Summable.of_norm_bounded hS (fun z=> (ht z).1.tasting _ _ hi _)
   have hP x (hx:x∈Set.Icc (0:ℝ) 1) q: Real.exp (P x q)=Fp x q:=by
      let P' z:=paths M g H (χ:=χ) z V x q; let e:=Ink.span M H; let g' := fun z=> P' (e.symm z)
      have he:= (Resin.emergent M g H χ hq V F x hx q).2.2
      have hp: Summable g':= (e.symm.summable_iff).mpr (hsum _ hx q)
      unfold P; change Real.exp (∑' z,P' z)=Fp x q; rw [← Equiv.tsum_eq e.symm, show ∑' z,P' (e.symm z)=_ from hp.tsum_sigma];
      have hv (z:H.fragrances):(∑' s, g' ⟨z,s⟩)= Palette.song M H χ g z V x q:=by rw [tsum_fintype]; exact Ink.tally M g H V z x q (χ:=χ)
      simp_rw [hv]; exact he
   let w:=Fp 0 ∅; have hh : H.homesteadPool χ V=w:=by
      unfold w Fp; simp_rw [Palette.offWays,muted]; rfl
   have hx : (0:ℝ)∈Set.Icc (0:ℝ) 1:=⟨le_rfl,zero_le_one⟩
   rw [hh,← show Real.exp (P 0 ∅)=w from hP 0 hx ∅,← Real.exp_add]
   convert hP i hi p using 2
   unfold bouquet P; simp_rw [Ink.units]; rw [(hsum i hi p).tsum_sub (hsum _ hx _),sub_add_cancel]
local notation "B'" => (Beam.marquee H P')
local notation "P₀" => posting P' H
-- main unmarked orientation equality. Need projected kernel before stance.
omit h he hq hB
section unmarked
open ConnectedActivityE6.Blaze.March Extra.Iteration Captain
variable {G0 q' ξ θ Λ κ t' : ℝ}{x:Config G c} (N : Captain H j C' d v t' G0 a r B D k χ) (γ : ℝ)
variable (hP : P'.order≤j) (hn : T.down.Bounds T.low σ θ Λ) (hZ: Cash.Renewed n ξ e D' H)
include N Γ F hP hn hZ
lemma untie :
    let r:= (posting P' H).read (plusone H Γ χ γ)
    Real.exp (Song.weighty H χ F* Fintype.card (Site c)- T.down.inChannels T.low P' R.beta V - r.additive P' V)*Real.exp (-γ* Collection.receipt T.down T.low P' V)= V0*H.homesteadPool χ V := by
  intro r; have ht t := Song.language P' H Γ χ N hp hP γ hZ hn (Seat.view t V)
  have hz : ∀ t: Seat c, HasSum (fun i=> masked P'.threshold (Song.scaleT P' H i).support (Song.opus H Γ χ γ i) (Seat.view t V)) (-(Real.log (H.homesteadPool χ V)) + (-(γ*Collection.receipt T.down T.low P' V+(R.beta*(billOf P' T.down.cubic V+billOf P' T.down.quartic V)+billOf P' T.down.loop V)))) := by
    intro t; have hb:= ht t; rw [Song.harmony χ hZ V t,Seat.view, Collection.receipt, Song.layer_spread,
      Song.bill_spread P' _ hn.width hn.three, Song.bill_spread P' _ hn.width hn.four, Song.bill_spread P' _ hn.width hn.two] at hb; exact hb
  have hd := voices (scaleT P' H) (opus H Γ χ γ) P' V _ hz
  have hL : r.additive P' V=_ := ((pennant H).hasSum_iff.mpr hd).tsum_eq
  rw [← Real.exp_add,chan,hL, Song.grants P' (J:=H) χ F hp V]
  have hv : 0<H.homesteadPool χ V:= by rw [← (H.threshold_logPool χ V hZ).2]; positivity
  rw [← show Real.exp (Real.log (H.homesteadPool χ V))= H.homesteadPool χ V from Real.exp_log hv,← Real.exp_add,Real.log_exp]; apply congr_arg Real.exp; ring
end unmarked

end Heron
end YM.RGComparison01.Pledge
