import YM.LocalTaylorR2.Reset.Desk
import YM.LocalTaylorR2.Receipt
/-!
# Same support R2 re-expression bills, reaches physical β in a superpolynomial (in χ) mesh accuracy
 -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Recoil
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Gas Ursell Trees Multiple OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection UVNext Next.Scheduling Ovens Quotes
open Extra.Iteration RG.Shoot Push.SectorMeasure Supply Input Testing Push.PriceCompiler Org UVExtension
open ConnectedActivityE6 PhysicalNext PhysicalNext.Repeat Song Spire Orchard Mast Oasis PhysicalNext.Repeat.Legato
open Pert Pert.Kinetic Tail
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Progress.DirectedRecipe Roost Opera
variable {G:Gauge} {M: Metals G} {D:Rolls M.p} {A : Alloy M D} {m j N n:ℕ} (R:Factor A) (hp:Mallow.RG12.Earned (railD G) R.shape A.delay) {hG:G.Simple} (S : Uses R hG) {t':ℕ→ℕ}{B:Bid.Worth}{P':ℕ→ℝ}{Q:Bandage R P' B}(L:Cellar S t' Q)
    (hC:(Cellar.yard (roseA S) L).Makes)
    (H:Guide A.B R.shape N m n (S.realBeat 0 N n (m+1))) (O:Return.Wood A.B m n)
local notation "P" => A.B.a.clock
local notation "T" => A.B.a.params m
local notation "b" => A.B.a.budget m
local notation "x" => A.B.a.clock.hatBeta m
local notation "χ" => A.B.a.clock.hatBeta (m+1)
local notation "Jp" => A.B.a.clock.J (m+1)
local notation "Ip" => A.B.a.clock.J m
local notation "s!"=> A.B.a.S.side m n
local notation "Z!"=> Song.posting (b) H
set_option quotPrecheck false
local notation "V!"=> plusone H (RG01.Survive.identityX H) Chi.canonical (A.B.kin.alpha N m)
local notation "R₀"=> A.B.kin.path N m
local notation "A₀"=>A.B.kin.alpha N m
local notation "κ"=> A.B.a.clock.forcedAllowance m
local notation "F!"=> Opera.earlyFee (p:=R.expense) A.B N m (S.realBeat 0 N n (m+1)).beta

local notation "τ0"=> Song.weighty H Chi.canonical O
local notation "β1"=> (S.realBeat 0 N n (m+1)).beta
local notation "α1"=> (S.realBeat 0 N n m).beta
local notation "v0"=> (S.realBeat 0 N n m).v
local notation "M!"=> Full.mesh (s!)
local notation "θ"=> (b).threshold
open CalendarStep

include L
lemma corridors (q:ℕ): ∀ᶠ i:ℕ in atTop, (P).monitor i≤ (A.B.a.clock.hatBeta i) ∧ ∀ p:ℕ, 4 ≤ ((A.B.a.S.side i p)).val ∧
    Real.pi^2*(Full.mesh (A.B.a.S.side i p))*(2*(Fintype.card PlaqAxes:ℝ)*(2*(A.B.a.clock.hatBeta i))^9) ≤1/2 ∧
    (4*Real.pi^2*coefK*(2*(A.B.a.clock.hatBeta i))^9)*(Full.mesh (A.B.a.S.side i p)) ≤ ((2*(A.B.a.clock.hatBeta i))^q)⁻¹:=by
    let y:=Cellar.yard (roseA S) L; have h:(P).hatBeta =(y.path.levels.clock.hatBeta):=rfl -- i implicit? `P` independent
    let d:ℝ:=Fintype.card PlaqAxes
    have he:=stay y hG 9 (2*Real.pi^2*(2*d))
    have hk:=stay y hG (9+q) (4*Real.pi^2*coefK)
    filter_upwards [monitoring (A:=A) hG,he,hk] with i hx ht hw
    refine ⟨hx,fun p=>?_⟩
    have hb:= Return.enough_room A.B i p
    have hh:=coefK_pos; have hl:=A.B.a.fits.delayed i
    refine ⟨by omega,?_,?_⟩
    · have ha:|2*Real.pi^2*(2*d)|=2*Real.pi^2*(2*d):=abs_of_nonneg (by unfold d; positivity)
      apply (le_div_iff₀ zero_lt_two).2
      linarith only [show (2*(A.B.a.clock.hatBeta i))^9*(2*Real.pi^2*(2*d))*(Full.mesh (A.B.a.S.side i p)) ≤ 1 from ha ▸ ht p]
    rw [←one_div]
    apply (le_div_iff₀ (by positivity)).2
    have hr : _ ≤(1:ℝ):= show (2*(A.B.a.clock.hatBeta i))^(9+q)*(4*Real.pi^2*coefK)*(Full.mesh (A.B.a.S.side i p)) ≤1 from (abs_of_nonneg (by positivity : 0≤4*Real.pi^2*coefK)) ▸ hw p
    rw [pow_add] at hr; linarith only [hr]

variable (hk:Mallow.RG12.Earned (ticketD G) R.shape A.delay)
-- knee: comparison through exact config ledger. includes actual projection and pre-H01 soft error.
omit L
structure Knee (l:ℕ)(δ ε:ℝ)(O:Return.Wood A.B m n):Prop where
    den : (S.realBeat 0 N n m).eval=earlyValue Z! R₀ (T).clip b V! β1 (Song.weighty H Chi.canonical O) A₀
    allP : Stamped R₀ (T).clip b Z! V! (T).width (T).paths ((P).loopCap m) β1 (Song.weighty H Chi.canonical O) A₀ (regularNeed G b (T).clip (T).width (T).paths A₀ F!) κ (softNeed G b (T).clip (T).width (T).paths A₀ F!)
    main :
      let v:= interpret R H l true; let w:=interpret R H l false; let τ:=Song.weighty H Chi.canonical O
      Difference Z! R₀ (T).clip b V! v w A₀ ∧
      Stamped R₀ (T).clip b Z! v (T).width (T).paths ((P).loopCap m) β1 τ A₀ (regularNeed G b (T).clip (T).width (T).paths A₀ (F!+ε)) κ (softNeed G b (T).clip (T).width (T).paths A₀ (F!+ε)) ∧
      (β1+A₀+Averaging.delta ((Z!).read v)-α1 ≤ ε/θ^2+δ ∧ α1-(β1+A₀+Averaging.delta ((Z!).read v))≤ε/θ^2+δ) ∧
      Collection.vac (V!) τ=v0 ∧ |v0-Collection.vac v τ| ≤ ε ∧
      |α1-(β1+A₀+Averaging.delta ((Z!).read V!))|≤ δ ∧
      -- these bills only: `fees` may fail. Quotes for full and for main retained also state what remains to pay.
      Stamped R₀ (T).clip b Z! w (T).width (T).paths ((P).loopCap m) 0 0 0 ε κ (ε/θ)
    rotor : θ⁻¹≤ Real.sqrt χ

include hp hk L hC
lemma readback (p l:ℕ)(ε c:ℝ)(hy:l≤ Jp)(he:0<ε)(hf:ε ≤1)(hz: loss Jp≤ε/2)(hm:m<N)(hH:RG01.Vacuum.delivered S N m n H)(hX:χ^requested (l+1) ε≤c)
    (hr:(P).monitor m≤ x)(hb:4≤ (s!).val)(h1: Real.pi^2*M!*(2*(Fintype.card PlaqAxes:ℝ)*(2*x)^9) ≤1/2)(h2:(4*Real.pi^2*coefK*(2*x)^9)*M! ≤ ((2*x)^p)⁻¹):
    Knee R S H l ((χ^p)⁻¹) c O := by
   obtain ⟨hl,hB⟩:= (S.ticking N n (Uses.centerP _)).prices (m+1) (Nat.zero_le _) hm
   let β:= S.realBeat 0 N n m
   have hw:= (valid_spine R S L hC).represents N n m hm.le
   have HU : β.eval=earlyValue Z! R₀ (T).clip b V! β1 τ0 A₀:= (weighs R S L hC H hk l ε O hm hf hy (hz.trans (by linarith)) hH).den
   obtain ⟨Ht,hV,hK⟩:= assay R hp H O hG hH hm hl hB (show β.p=b from hw.vac) hw.band hw.good HU hr hb h1
   have hj : 1≤ χ:= (A.B.a.fits.delayed _).le; have hq := zero_lt_one.trans_le hj
   have hδ : χ ≤ 2*x:= by rw [PriceCompiler.beta_eq A.B.valid]; exact (gatesHere R hp).gap
   let u:=β1+A₀; let d(v: Collection.Source G s!):= u+Averaging.delta ((Z!).read v)
   have ha: |α1-d V!| ≤ (χ^p)⁻¹ := ((hK.trans h2).trans (inv_anti₀ (by positivity : 0 < (χ^p)) (pow_le_pow_left₀ hq.le hδ _)))
   refine ⟨HU,Ht,?_,?_⟩
   · intro v w t
     let k:= ε/2; let e:=χ^requested (l+1) k
     have hp':= Real.rpow_pos_of_pos hq (requested (l+1) k)
     have hk' : e ≤ c:= (Real.rpow_le_rpow_of_exponent_le hj (show requested (l+1) k ≤ requested (l+1) ε from by unfold k requested; linarith)).trans hX
     have hb': χ^(loss Jp/2)*e≤ c:=by unfold e; rw [← Real.rpow_add hq]; exact (Real.rpow_le_rpow_of_exponent_le hj (by unfold k requested; linarith)).trans hX
     obtain ⟨hv,hW,hA,hL,h₀,hF,hE,hG'⟩:= transmit R H O hH hm hl hB hk l hy k hz
     obtain ⟨hX',hY,hK',hj',he'⟩:= mails R H O hH hm hl hB hk l hy k hz hG
     have ha':= (paid R hp H hm).2.2 e hp'.le
     have hP := (b).threshold_pos
     refine ⟨painted hF hG A₀ hE hv hW hA, tariff R hG hm hl hB _ _ _ _ _ _ _ (fullLocal hE (add_le_add_right hk' _) le_rfl), ?_,hV.symm,?_,ha,enlarge (tariff R hG hm hl hB _ _ _ _ _ _ _ hX') (ha'.1.trans hb') le_rfl ((le_div_iff₀ hP).mpr ?_)⟩
     · have hr:θ^2*|Averaging.delta ((Z!).read w)| ≤ e:=hY
       have hJ:= (le_div_iff₀ (sq_pos_of_pos hP)).2 (show |Averaging.delta ((Z!).read w)| * θ^2 ≤ c by rw [mul_comm]; exact hr.trans hk')
       have hh : |α1-d v| ≤ c/θ^2+ (χ^p)⁻¹:= by rw [show α1-d v= Averaging.delta ((Z!).read w) + (α1-d V!) by unfold d v w; linarith only [he']]; exact (abs_add_le ..).trans (add_le_add hJ ha)
       change d v-α1≤ c/θ^2+(χ^p)⁻¹ ∧ α1-d v≤ _
       exact ⟨(le_abs_self _).trans ( (abs_sub_comm ..).trans_le hh),(le_abs_self _).trans hh⟩
     · change |β.v - Collection.vac (interpret R H l true) τ0| ≤ _
       rw [hV,hj']; exact hK'.trans hk'
     rw [mul_comm]; exact ha'.2.trans hb'
   · apply (inv_bound A.B.a m).trans
     apply Real.sqrt_le_sqrt
     rw [PriceCompiler.beta_eq A.B.valid]; have hs := G.slopeConstant_pos hG
     exact le_add_of_nonneg_right (mul_nonneg hs.le (Real.log_nonneg (by exact_mod_cast (D.L Jp).pos)))
end YM.LocalTaylorR2.Recoil
