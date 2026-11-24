import YM.MSbar.Mosaic.Chord
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.MSbar.Mosaic
open Function Filter MeasureTheory Precision Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Gauge Midpoint Rolling Exterior Wilson Wave Lis Cypress Topology
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal Further.GaussianScalar Jade Kelvin Bout Parma Tramp Heath Stock Heath.Cottage Film
open Measuring Cane Laurent Bloch UVNext.PricedKernels Spruce Lapaz
open Next.SectorChange Bulk Posture JetTab
variable {G:Gauge}
namespace Issue
variable {ι:Type}{X f' g H0:ι→ℝ}{A:ι→Issue G}{φ:Filter ι}[φ.NeBot] (hX:Tendsto X φ atTop) (χ:ChartRatio G)(J:Voice G)(H H':Stage)(K:Patch)(D:KernelChoices)
variable (hG:G.Simple) (hD:K.Branches D G)(hQ: Clear G J)(hχ:LocalRatio χ)
local notation "α'" i=> tip G K.L (X i)
local notation "Y"=> fun i:ι=> tip G K.L (X i)
local notation "w'" i=> vol (tip G K.L (X i))
local notation "t'" i=> (A i).fClock
variable (hp:∀ᶠ i in φ,Paid (A i) K H H' J (X i)) (hq:∀ᶠ i in φ,(A i).S.kernel=D)
variable (W:(i:ι)→Positions (Primary (A i).c G))(hW:∀ᶠ i in φ,‖W i‖ ≤ hull (X i))
variable {p m k q L:ℕ}
variable (M:StageCost)(i':G.ColorIndex){s' e ν b:ℝ}(hc:∀ᶠ i in φ,Festival (A i) χ p i' ∧ ClockD (A i) p m M.s (X i)∧ Cs (A i) χ M.s p m (X i) i' (f' i) b ∧ Issue.Receipt (A i) M (X i))
variable (z:(i:ι)→Site (A i).f)
variable (hR:∀ᶠ i in φ,Ore M (X i) K)
variable (P:Palisade){τ b':ℝ}(B :ℝ)
local notation "x'" i=> boxX (tip G K.L (X i)) (z i)
local notation "x₁" i=> boxY (tip G K.L (X i)) (z i)
local notation "N"=> k*(p+2)
local notation "N'" i=> Fintype.card (Lake (A i).F (boxX (α' i) (z i)) G)
local notation "N₁" i=> (keepB (A i).F (x' i) G).card
local notation "N₂" i=> (keepF (A i).F (x' i)).card
local notation "Γ" i=> Ruby.crownP (A i).F (A i).M (W i)
local notation "Φ'" i=> inkW (N₂ i)
variable (h₁:p+2≤ m)(ha:Run φ X f' 0)(hk:k=m+1)(hT:p+3≤ k)(hμ:4 ≤ m)(hb:0<τ)(hb':0≤b')
local notation "γ" i=> thorn (Y i) (k*(p+2))
variable (hK:∀ᶠ i in φ, Issue.Buy (A i) (W i) (boxX (tip G K.L (X i)) (z i)) (boxY (tip G K.L (X i)) (z i)) J P χ (tip G K.L (X i)) e s' (thorn (tip G K.L (X i)) (k*(p+2))) τ b')
include hX hp hc hR hW hχ hG hQ h₁ ha hk hT hμ hb hb' hq hK
-- choose Local Forecast any L size; Step Sensor ACK. require Hat mask chosen.
variable (F:ι →ℝ→ℝ)(hG0:∀ᶠ x in φ,Lodge.Hat k (vol (tip G K.L (X x))) (g x) (F x)∧1 ≤ g x) (hg:Run φ (fun i=>tip G K.L (X i)) g 0)
-- minX.R.
omit hp hc hR hW hχ hG hQ h₁ ha hk hT hμ hb hb' hq hK
lemma plume(a b v:ι→ℝ)(hv:Run φ X v (epsW p))(he:Run φ X a 0)(hk:Run φ X b (pawn p))(ht:Run φ X g (-(1/2)))(k:ℕ):
         let H(i):=cornP (a i) k k
         let A(i):= b i+scratch (a i) k (b i) k
         Run φ X (fun i=>coins (a i) (H i) (A i) (v i) (g i) p k) (epsW p):=by
      intro H A; let ε:=epsW p; let S:=pawn p; obtain ⟨hy,hP,hQ⟩:=mp0 p; let j:=-(1/2:ℝ); have hy:j+(pawn p) ≤ ε:=by unfold j ε epsW; linarith only
      have hD:(pawn p)*2 ≤ ε:=by unfold ε epsW; linarith only [hQ]
      have hM:(pawn p) ≤ 0:=hQ.trans (by norm_num); have he':Run φ X H 0 :=(Run.token hX 1|>.addR hX (Run.mulK hX he _)).Ypow hX _
      have hC(j:ℕ) : Run φ X (fun i=>scratch (a i) k (b i) j) S:=by
            induction j with
            |zero=> simp only [scratch]; intro r he; filter_upwards [hX.eventually_ge_atTop 0] with i hx; rw [abs_zero]; positivity
                                                                                          
            |succ j ih=> unfold scratch; exact ih.addR hX (((ih.Yrat hX he).addR hX (Run.Ycost hX he' hk)).mulK hX _)
      have ha:Run φ X A S:= hk.addR hX (hC _); have hh(j:ℕ):Run φ X (fun i=>coins (a i) (H i) (A i) (v i) (g i) p j) ε:=by
          induction j with
          | zero=> simp only [coins]; intro r he; filter_upwards [hX.eventually_ge_atTop 0] with i hx; rw [abs_zero]; positivity
          | succ i ih=>
              have hS:=ha.loosen hM; have hm:=ih.loosen (hP.le.trans hM); unfold coins; refine Run.addR hX (ih.addR hX hv) ?_; refine Run.mulK hX ?_ _; unfold Cypress.tape; apply Run.addR hX
              · apply Run.addR hX
                · exact ((((Run.Yrat hX hv ((he.addR hX hS).addR hX hm)).addR hX (Run.Ycost hX (he'.addR hX hS) ih)).addR hX (((ht.Yrat hX he).mulR hX ha).loosen hy)).addR hX ((ha.raise hX 2).loosen (by exact_mod_cast hD)))
                exact (((ht.Yrat hX he').mulR hX ha).loosen hy)
              exact Run.Yrat hX (Run.tr hX ht) (he'.Ymul hX he)
      exact hh _
include hp hG
lemma fat : ∀ᶠ i in φ, αm (X i)/(K.L.val:ℝ) ≤ αm (tip G K.L (X i)):=by
     filter_upwards [hp,hX.eventually (Alto.drift_scale hG K.L)] with i he hx; obtain ⟨hx,hY,hz⟩:=hx; let u:= Alto.flurry (X i); let v:=Alto.flurry (Y i); have hv:0<u:= zero_lt_one.trans_le hx; have hh:u≤v:=hY; have he':v ≤ 1.1*u:=hz
     have hp:3 ≤ (K.L.val:ℝ):=by exact_mod_cast K.coarse
     have hu: v^3≤ u^3*(K.L.val:ℝ):=by apply (pow_le_pow_left₀ (hv.le.trans hh) he' 3).trans; rw [mul_pow]; rw [mul_comm (u^3) (K.L.val:ℝ)]; apply mul_le_mul_of_nonneg_right; norm_num; linarith only [hp]; positivity
     unfold αm; simp_rw [_root_.zpow_neg]; change ((u^3:ℝ))⁻¹/(K.L.val:ℝ) ≤ (v^3:ℝ)⁻¹; have hg:= (hv.trans_le hh); apply le_trans (le_of_eq _) (inv_anti₀ (by positivity) hu); rw [_root_.mul_inv,div_eq_mul_inv]; rfl -- names
include hc hR hW hχ hQ h₁ ha hk hT hμ hb hb' hq hK hG0 hg
-- generalized summit.Pointwise low.Rank via weight estimate all anchors
lemma fireball : ∃ g':ι→ℝ,Run φ Y g' (pawn p) ∧∀ᶠ i in φ,0 ≤ g' i∧∀ l:List (Primary (A i).c G),l≠[]→ l.length≤ k→ |Issue.phiB (A i) p (W i) (F i) l| ≤g' i:=by
    let S:=Y; let U(i):= 5*goalP (S i) p; let L:ℝ:= K.L.val; have hZ:Tendsto S φ atTop:= (Work.E09.betaF_growth G K.L).comp hX; have hU:Run φ S U (pawn p):= (Run.core hZ _).mulK hZ _
    let E(i):= U i*L^4; have he':Run φ S E (pawn p):= hU.mulY hZ _; refine ⟨E,he',?_⟩
    filter_upwards [hK,hc,hR,hp,gate hX hG hX K.L N,hG0,hZ.eventually_gt_atTop 1,(Alto.broad.comp hZ).eventually_ge_atTop 32, fat hX J H H' K hG hp] with i hK ⟨he,hQ,hP,hV⟩ hr hh ha ⟨hC,hI⟩ hs hS hL; let A':=A i; let f':= A'.preY p; let M':= A'.M; let v:= vol (S i);
    have hu :0< S i:=zero_lt_one.trans hs
    have hT:1 ≤ v :=by have hv: 32 ≤ hatW (S i):=hS; unfold v vol; linarith only [hv]; -- done
    have hv :0 ≤ U i:= by unfold U goalP; positivity
    have hz:L= A'.S.ratio.count.val:= Nat.cast_inj.mpr ((congr_arg (fun x:Patch=>x.L.val) hh.space).symm); have H': (A i).passage (X i)=(S i):=by unfold passage; rw [hh.space]; -- syntax
    have hw:=hQ.turns; have hb:= hQ.beam; rw [H'] at hw hb; let a:= αm (S i); let b:= αm (X i); have hρ:0≤ a:= le_trans (mul_nonneg (Nat.cast_nonneg _) ha.1.le) ha.2.1; have he':0<v:= zero_lt_one.trans_le hT
    have hA(j:ℕ)(hζ:j ≤ m): JetTab (Measuring.chart A'.f G) a M.s v (Metric.closedBall 0 v) f' j (U i) := JetTab.levelAll he' hρ hb hw hμ le_rfl j hζ
    have hS: Lodge.Vase f' k (U i) v:=by rw [hk]; exact Lodge.cs (fun i' hi=> hA i' (by omega)) hb hT hρ (Nat.zero_lt_succ _)
    refine ⟨mul_nonneg hv (pow_nonneg (Nat.cast_nonneg _) _),fun l he' hL' =>?_⟩; cases l with
    | nil=>exact (he' rfl).elim
    | cons j l=>
         let Ω:= Measuring.chart (A i).c G; let m0: Solver .. := hK.fast; let α:= StageCost.A M -- no
         have hF: b/(A'.S.ratio.count.val:ℝ) ≤ a:= by rw [← hz]; exact hL
         have hv0:= zero_lt_one.trans_le hT; obtain ⟨f,hf,hh⟩:= Cypress.token (A i).F A'.pre A'.v A'.fClock A'.ρ A'.T (F i) M' he.critical he.guessed hV.slope (hK.fast.bids) (fun i'=> (le_abs_self _).trans (hK.fast.growth.single (by exact add_nonneg le_rfl ha.1.le) _ _)) hF hC hS hv0 hL' (hA l.length (by simp only [List.length_cons] at hL';omega)) -- note he name.He shadow nil
         let Y'(l:List (Primary A'.c G)):= f (j::l)*swipe Ω b M.s (j::l)
         have hg : f (j::l) ≤Y' l:= le_mul_of_one_le_right (hf (j::l) rfl|>.1) (w_start hV.slope.a0 M.s _)
         -- need lit only lists length m.P.Lit requires all, patch outside m to0
         have hy:Y' l ≤ Yarn l.length Y':=by
              let E(t:List (Primary A'.c G)):=if t.length=l.length then Y' t else 0; have hp:Y' l= E l:=by simp [E]
              rw [hp,←show Yarn l.length E= _ from stitch l.length (g:=Y') (f:=E) (fun i hh=> by unfold E;rw [if_pos hh])]; refine lit l E (fun i=>?_); unfold E; split; next hs=> exact mul_nonneg (hf (j::i) (by simp [hs])|>.1) (effect ..|>.le)
              next hh=>rfl
         refine ((hf (j::l) rfl).2 _).trans (hg.trans (hy.trans ((hh j).trans ?_)))
         let v':= (Cane.value b M.C M.A M.E M.s M.sway); have hS: v'/L ≤ (1/128:ℝ):= hr; have hL:0 ≤ L:=Nat.cast_nonneg _; rw [← hz]; refine (mul_le_of_le_one_right (mul_nonneg (div_nonneg hv (pow_nonneg hv0.le _)) (pow_nonneg hL _)) (pow_le_one₀ (div_nonneg (Cane.specs _ hV.slope) hL) (hS.trans (by norm_num)))).trans ?_; -- he' shadow
         exact mul_le_mul_of_nonneg_right (div_le_self hv (one_le_pow₀ hT)) (pow_nonneg hL _)
end Issue
end YM.MSbar.Mosaic
