import YM.WilsonCoeffUV.Vacuum.UV.FirstLoop
import YM.Price.Waits
/-!
# Price demands on supplied schedule

Dropped behind unmarked? Can buy these across whole deeper UV tail for *all*
orders at once, each demand starts on tail, crossing both overlap types.
Only `Levels` with pre floors and structural beta delay(s) required here, never
pretune all `Family`. Use from same physical object with explicit h's; not implied
by UV Final. Conditional for that adapter.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Next.Free Extension.UV.Linear PathCost Realm PowerSeries Supply
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{K:KernelChoices}{A A':Levels G}{n N M e m m' i k r b j l:ℕ}

-- use actualized from canonical pre

lemma couponUnit (G:Gauge)(K: KernelChoices)(i j : ℕ)(p:4 ≤ i)(v:5 ≤ j): ∃ T:Tokenizer K G i j, T.s ≤ 1 := by
    let T : Tokenizer K G i j := Classical.choice (current_stamp _ _ p v)
    refine ⟨{ T with
      s:= min T.s 1
      sigma:=lt_min T.sigma one_pos
      port:=fun A m u v e=> (T.port A m u v e).shrinks A m (min_le_left ..) }, min_le_right ..⟩

def cue (G:Gauge)(K:KernelChoices)(i j)(h:4 ≤ i)(t:5≤j): Tokenizer K G i j:= (couponUnit _ _ i j h t).choose
lemma cue_unit (p:4 ≤ i)(v:5≤j) : (cue G K i j p v).s ≤ 1:= (couponUnit G K i j p v).choose_spec
lemma upstairs (A:Levels G)(m)(h:5≤A.clock.J m): 5≤ A.clock.J (m+1):= h.trans (A.fits.mono (by omega))
def craftQuest (A:Levels G)(m n)(h:5≤A.clock.J (m+1)) := Craft (cue G A.clock.kernel (A.clock.J m) (A.clock.J (m+1)) (A.clock.adm _) h) (cue G A.clock.kernel (A.clock.J (m+1)) (A.clock.J (m+2)) (A.clock.adm _) (upstairs A _ h)) n (A.S.block m).val
def quest (A : Levels G)(m:ℕ)(Ñ:ChartRatio G){n}(h:5≤A.clock.J (m+1))(p:craftQuest A m n h): Usage A Ñ m := visits Ñ _ _ p

lemma desired (G:Gauge)(K:KernelChoices)(e j:ℕ): ∀ᶠ L:ℕ in atTop,∀ (A:Levels G)(m:ℕ),A.clock.kernel=K  →  A.clock.J (m+1)=j  →  (A.S.block m).val=L → ∀ h:5 ≤ A.clock.J (m+1), craftQuest A m e h:=by
   have hx (i l):∀ᶠ L:ℕ in atTop,∀ (A:Levels G)(m:ℕ),A.clock.kernel=K  →  A.clock.J (m+1)=j  →  (A.S.block m).val=L → ∀ h:5 ≤ A.clock.J (m+1), A.clock.J m=i  →  A.clock.J (m+2)=l  →  craftQuest A m e h:=by
       by_cases H:4≤ i ∧ 5≤ j ∧ 5≤ l
       · obtain ⟨h,t,b⟩:=H
         filter_upwards [Craft.demand (cue G K i j h t) (cue G K j l (by omega) b) e] with L he
         intro A m hK hj he' hb hh hl; subst L K i l j; exact he
       apply Eventually.of_forall; intro l' A m h hj ht hx' hb ho; subst l' K j l i; exact False.elim (H ⟨A.clock.adm _,hx', upstairs A _ hx'⟩)
   let S:= Finset.range (j+2)
   filter_upwards [(eventually_all_finset S).mpr fun i _=> (eventually_all_finset S).mpr fun l _=> hx i l] with L hv
   intro A m hK hj ht hg
   have he: A.clock.J (m+2)≤A.clock.J (m+1)+1:= A.fits.stepSlow (m+1); have hz:A.clock.J m≤ A.clock.J (m+1):= A.fits.mono m.le_succ
   exact hv _ (show A.clock.J m ∈ S from Finset.mem_range.mpr (by omega)) _ (show A.clock.J (m+2)∈ S from Finset.mem_range.mpr (by omega)) A m hK hj ht hg rfl rfl
-- Gear identity; even when a depends on A typed proofs heterogeneous
private lemma token_eq (f:∀ (K:KernelChoices) (i j:ℕ), Tokenizer K G i j → ℝ) {K K':KernelChoices} (w:K=K')(u:i=b)(v:j=k){p:4 ≤ i}{t:5 ≤ j}{q:4 ≤ b}{s:5 ≤ k}: f K i j (cue G K i j p t) = f K' b k (cue G K' b k q s):=by subst_vars; rfl
lemma twinning {A A':Levels G}{Ñ:ChartRatio G} (h:A'.clock.kernel=A.clock.kernel)(hb:A'.clock.J m'=A.clock.J m)(ht:A'.clock.J (m'+1)=A.clock.J (m+1)) (hx:A'.clock.J (m'+2)=A.clock.J (m+2))(he:A'.S.block m'=A.S.block m)
   (p:5≤A.clock.J (m+1))(p':5≤A'.clock.J (m'+1))(hm:craftQuest A m n p)(hp:craftQuest A' m' n p'): (quest A m Ñ p hm).gear = (quest A' m' Ñ p' hp).gear := by
    have hw: loose A m=loose A' m':= by
       have hh:(loose A' m').J=(loose A m).J:= ht; have hv:(loose A' m').L=(loose A m).L:=he; cases g:(loose A m); cases g':(loose A' m'); simp_rw [g,g'] at hh hv; subst_vars; rfl
    let P:= quest A m Ñ p hm; let Q:= quest A' m' Ñ p' hp
    -- Gear has no ext by default
    unfold quest Usage.gear
    congr 1
    all_goals try first | exact hw | exact h.symm
    case e_past => exact token_eq (fun _ _ _ x=> x.outlet) h.symm ht.symm hx.symm
    case e_s => exact token_eq (fun _ _ _ x=> x.s) h.symm hb.symm ht.symm
    case e_σ=> exact token_eq (fun _ _ _ x=>x.outlet) h.symm hb.symm ht.symm
    case e_preB=> exact token_eq (fun _ _ _ x=>x.preB) h.symm hb.symm ht.symm
    case e_sig=> exact token_eq (fun _ _ _ x=>x.sig) h.symm hb.symm ht.symm
    case e_D=> dsimp only [visits]; rw [hw]; exact token_eq (G:=G) (fun _ _ _ x=>x.bid (loose A' m')) h.symm hb.symm ht.symm
lemma match_escrow {Ñ:ChartRatio G}{I:Usage A Ñ m} {J:Usage A' Ñ m'} (p:I.gear=J.gear)(a:A'.clock.kernel=A.clock.kernel)(h:A'.clock.J m'=A.clock.J m)(g:A'.S.block m'=A.S.block m){c:ℝ}(e:Escrow I n c): Escrow J n c:=by
   have he:I.σ=J.σ:= congr_arg Gear.σ p
   refine ⟨fun j t=>by rw [←p, arch, g,← arch]; exact e.gain _ t, fun j t=>by rw [←p]; exact e.enough _ t,by rw [a,h]; exact e.capital,fun k r t x=>?_ ,fun k r t x=>by rw [←p]; exact e.burst _ _ t x,fun k r t x=>by rw [←p]; exact e.boom _ _ t x,by rw [g]; exact e.height,by rw [←he]; exact e.width_bill,by rw [←he]; exact e.flash,by rw [← show I.D=J.D from congr_arg Gear.D p]; exact e.freight⟩
   rw [← show _= oreD _ _ _ _ _ from (show oreD G r k I.σ I.width=oreD G r k J.σ J.width by congr 1)]; exact e.stowage k r t x
lemma deferred (K:KernelChoices)(L:Side)(j e:ℕ)(Ñ:ChartRatio G): ∀ᶠ c:ℝ in atTop,∀ (A:Levels G)(m:ℕ), A.clock.kernel=K  →  A.clock.J (m+1)=j  →  A.S.block m=L  → ∀ (h:5≤A.clock.J (m+1))(p:craftQuest A m e h), Escrow (quest A m Ñ h p) e c:=by
    have hx (i l):∀ᶠ c:ℝ in atTop,∀ (A:Levels G)(m:ℕ), A.clock.kernel=K  →  A.clock.J (m+1)=j →  A.clock.J m=i  →  A.clock.J (m+2)=l  →  A.S.block m=L  → ∀ (h:5≤ A.clock.J (m+1))(p:craftQuest A m e h),Escrow (quest A m Ñ h p) e c:=by
       by_cases H: ∃ (A:Levels G)(m:ℕ),A.clock.kernel=K ∧ A.clock.J (m+1)=j ∧ A.clock.J m=i ∧ A.clock.J (m+2)=l ∧ A.S.block m=L ∧ ∃ h:5≤A.clock.J (m+1), craftQuest A m e h
       · obtain ⟨A,m,r,w,u,v,z,h,p⟩:= H; subst K i l j L
         filter_upwards [cooled Ñ _ _ p] with c hc; intro A' m' i j b t e h' p'; exact match_escrow (twinning i b j t e h h' p p') i b e hc
       apply Eventually.of_forall; intro c A m he ht hp b x h p; exact False.elim (H ⟨_,_,he,ht,hp,b,x,h,p⟩)
    let S:= Finset.range (j+2)
    filter_upwards [(eventually_all_finset S).mpr fun i _=> (eventually_all_finset S).mpr fun l _=>hx i l] with c h
    intro A m a b c' e p
    have he: A.clock.J (m+2)≤A.clock.J (m+1)+1:= A.fits.stepSlow (m+1); have hz:A.clock.J m≤ A.clock.J (m+1):= A.fits.mono m.le_succ
    exact h _ (show A.clock.J m∈ S from Finset.mem_range.mpr (by omega)) _ (show A.clock.J (m+2)∈ S from Finset.mem_range.mpr (by omega)) A m a b rfl rfl c' e p

namespace Ticket
open Real
-- canonical demands; downstream may adjust J horizons.
def floors (G:Gauge)(K:KernelChoices)(X:ℕ → ℕ)(j:ℕ):= (eventually_atTop.mp (desired G K (X j) j)).choose
lemma afforded {p:Sheet G}{W:Rolls p}(a:A.clock.kernel=p.kernel) (e:A.clock.factor=W.L)(X:ℕ → ℕ)(h:p.floorL≥ floors G p.kernel X)(k:ℕ)(ht:5≤A.clock.J (k+1)): craftQuest A k (X (A.clock.J (k+1))) ht:=by
   let i:= A.clock.J (k+1); have he:= A.fits.sameFactor k; rw [e] at he
   have hp:floors G p.kernel X i ≤ (A.S.block k).val:=le_trans (h i) ((W.large i).need.trans (le_of_eq (congr_arg Subtype.val he)))
   exact (eventually_atTop.mp (desired G p.kernel (X i) i)).choose_spec _ hp A k a rfl rfl ht

def delayCost {p:Sheet G}(W:Rolls p)(X:ℕ → ℕ)(Ñ:ChartRatio G)(j:ℕ):= (eventually_atTop.mp (deferred p.kernel (W.L j) j (X j) Ñ)).choose

lemma further {A:Levels G}{Ñ:ChartRatio G}{I:Usage A Ñ m}{c C:ℝ}(p:Escrow I n c)(u:b≤ n)(t:c≤C): Escrow I b C := ⟨fun i e=>p.gain i (by omega),fun i e=>p.enough i (by omega),p.capital.trans t,fun k r v h=>(p.stowage k r (by omega) (by omega)).trans t,fun k r a b=>(p.burst k r (by omega) (by omega)).trans t,fun k r a b=>(p.boom k r (by omega) (by omega)).trans t,p.height.trans t,p.width_bill.trans t,p.flash.trans t,p.freight.trans t⟩
-- hat z from same Schedule. allow absolute `y` reference and explicit Λ later

def zz (A:Levels G)(m:ℕ):= 1+ Real.log (Real.log (A.clock.hatBeta m))
private def stopB (G:Gauge)(u:ℝ):= max G.slopeConstant (exp (exp (max u 1)))
lemma escalator {u:ℝ}(v:stopB G u ≤ A.clock.hatBeta m): G.slopeConstant ≤ A.clock.hatBeta m ∧ 1 ≤ Real.log (A.clock.hatBeta m) ∧ u≤ zz A m:=by
   have he:= le_trans (le_max_right ..) v
   have hv : exp (max u 1) ≤ Real.log (A.clock.hatBeta m):= by rw [← Real.log_exp (exp (max u 1))]; exact Real.log_le_log (by positivity) he
   have hk : u≤ Real.log (Real.log (A.clock.hatBeta m)):= by refine (le_max_left u 1).trans ?_; rw [← Real.log_exp (max u 1)]; exact Real.log_le_log (by positivity) hv
   exact ⟨le_trans (le_max_left ..) v,le_trans (Real.one_le_exp (x:=max u 1) (le_max_of_le_right zero_le_one)) hv,by unfold zz; linarith⟩
lemma hat_up (g:G.Simple)(p:m≤ n): A.clock.hatBeta m ≤ A.clock.hatBeta n:= add_le_add_right (mul_le_mul_of_nonneg_left (PathCost.scales _ p) (Gauge.slopeConstant_pos g).le) _
lemma rootCost (g:G.Simple)(u:m ≤ n)(p:G.slopeConstant ≤ A.clock.hatBeta m)(he:1≤ Real.log (A.clock.hatBeta m)): zz A m≤ zz A n ∧ zz A n ≤ zz A m+(A.S.scale n-A.S.scale m):=by
    let x:= A.clock.hatBeta m; let y:= A.clock.hatBeta n
    let d:= A.S.scale n-A.S.scale m
    have hx:0<x:= lt_of_lt_of_le (Gauge.slopeConstant_pos g) p
    have hb:1≤Real.log x:=he
    have hd:0 ≤ d:= sub_nonneg.mpr (scales A.S u)
    have hy:x ≤ y:= hat_up g u
    have h :y=x+G.slopeConstant*d:=by unfold x y d Calendar.hatBeta; ring
    have ha:= Real.log_le_log hx hy
    have hr: Real.log y- Real.log x ≤ d := by
        rw [← Real.log_div (hx.trans_le hy).ne' hx.ne']; refine (Real.log_le_sub_one_of_pos ?_).trans ?_
        · exact div_pos (hx.trans_le hy) hx
        have hv : y/x ≤ 1+d:= (div_le_iff₀ hx).mpr (by rw [h]; nlinarith [mul_le_mul_of_nonneg_right (show G.slopeConstant≤x from p) hd])
        linarith
    have ht: 0< Real.log x:=lt_of_lt_of_le zero_lt_one hb
    have hv: Real.log (Real.log y)-Real.log (Real.log x) ≤ d:=by
       have hp' := ht.trans_le ha
       rw [←Real.log_div hp'.ne' ht.ne']; have hv : Real.log y/Real.log x ≤1+d:= (div_le_iff₀ ht).mpr (by nlinarith)
       apply le_trans (Real.log_le_sub_one_of_pos (by positivity)); linarith
    change 1+Real.log (Real.log x)≤1+Real.log (Real.log y)∧1+Real.log (Real.log y)≤1+Real.log (Real.log x)+d
    exact ⟨by linarith only [Real.log_le_log ht ha],by linarith only [hv]⟩

def voucher {p:Sheet G}(W:Rolls p)(X:ℕ → ℕ)(Ñ:ChartRatio G) : ℕ → ℝ:=fun j=> stopB G (delayCost W X Ñ j)

lemma scriptVoucher {p:Sheet G}(W:Rolls p)(X:ℕ → ℕ)(Ñ:ChartRatio G)(j:ℕ){v:ℝ}(q:voucher W X Ñ j ≤ exp (exp (v-1))) : delayCost W X Ñ j≤ v:=by
    have h: exp (exp (max (delayCost W X Ñ j) 1))≤ exp (exp (v-1)):= (le_max_right ..).trans q
    simp only [Real.exp_le_exp] at h
    have hp:= le_max_left (delayCost W X Ñ j) 1; linarith
lemma scaledBills (A:Levels G) (m:ℕ): A.clock.hatBeta m=exp (exp (zz A m-1)):=by
    unfold zz
    rw [show 1+ Real.log (Real.log (A.clock.hatBeta m))-1=Real.log (Real.log (A.clock.hatBeta m)) by ring]
    rw [Real.exp_log (Real.log_pos (A.fits.delayed _)), Real.exp_log (lt_trans zero_lt_one (A.fits.delayed _))]
structure BasicBill {p:Sheet G}{w:Rolls p}{Ω:Protection w}(Y:Delays Ω) (A:Levels G) (y:ℕ → ℝ) (ℓ:ℕ): Prop where
    kernel : A.clock.kernel=p.kernel
    lengths : A.clock.factor=w.L
    pays m : ℓ ≤ m →  Y.betaEntry (A.clock.J (m+1)) ≤ exp (exp (y m-1))
    cut i: ℓ ≤ i → 1≤ y i
    age i j: ℓ ≤ i → i≤j → y j≤ y i+(A.S.scale j-A.S.scale i)

structure Marks (A:Levels G) (Ñ:ChartRatio G) (n anchor:ℕ) (y:ℕ → ℝ) where
    mass (i:ℕ):anchor ≤ i →  Usage A Ñ i
    takes i (p:anchor ≤ i): Escrow (mass i p) n (y i)
    overlap i (p:anchor ≤ i) : (mass i p).past≤(mass (i+1) (by omega)).σ
lemma Aval {Ñ:ChartRatio G}{y:ℕ→ ℝ} (P:Marks A Ñ n b y) (g:G.Simple)(h:LocalRatio Ñ)(ht:∀ i, b≤ i  → 1≤y i)(hg:∀ i j, b ≤ i →  i≤j →  y j≤ y i+(A.S.scale j-A.S.scale i)): ∃ R:Realm G n Credit.leanC,R.draws=A ∧ R.paid=Ñ ∧ R.y=y ∧ R.anchor=b:=by
   exact ⟨⟨A,Ñ,g,h,b,y,ht,hg,P.mass,P.overlap, fun i p=> by rw [Credit.lean_cost]; exact P.takes i p⟩,rfl,rfl,rfl,rfl⟩

variable {p:Sheet G}{W:Rolls p}{Ω:Protection W}{X:ℕ → ℕ}{Ñ:ChartRatio G} {Y:Delays Ω}{o:Bar Y}{b': Wait o}
lemma install_awards (g:G.Simple)(_:LocalRatio Ñ)(pL:floors G p.kernel X ≤ p.floorL)(a:Paid b' A)(hp:voucher W X Ñ ≤ Y.betaEntry) (ℓ n:ℕ)(hz:∀ i,ℓ ≤ i  →  5≤A.clock.J (i+1) ∧ n≤ X (A.clock.J (i+1))) : (∀ i,ℓ ≤ i → 1≤ zz A i) ∧ (∀ i j,ℓ≤ i →  i≤ j → zz A j≤ zz A i+(A.S.scale j-A.S.scale i)) ∧ Nonempty (Marks A Ñ n ℓ (zz A)):= by
    have he i : stopB G (delayCost W X Ñ (A.clock.J (i+1))) ≤ A.clock.hatBeta i:= le_trans (hp _) (a.pays i)
    have ht i:=escalator (he i)
    have hh i (p':ℓ≤ i):= afforded a.kernel a.lengths X pL i ((hz i p').1)
    refine ⟨fun i _=>by have he:= Real.log_nonneg (ht i).2.1; unfold zz; linarith,fun i j _ hk=>(rootCost g hk (ht i).1 (ht i).2.1).2,⟨fun i e=> quest A i Ñ (hz i e).1 (hh i e),?_,fun i g=>le_rfl⟩⟩
    intro i v; let j:=A.clock.J (i+1)
    have h : A.S.block i=W.L j:=by rw [←A.fits.sameFactor,a.lengths]
    have hb := (eventually_atTop.mp (deferred p.kernel (W.L j) j (X j) Ñ)).choose_spec (zz A i) (ht i).2.2 A i a.kernel rfl h _ (hh i v)
    exact further hb (hz i v).2 le_rfl

lemma booked (g:G.Simple)(a:Paid b' A)(hp:voucher W X Ñ≤Y.betaEntry) (ℓ):BasicBill Y A (zz A) ℓ:=by
    have he i := escalator (le_trans (hp _) (a.pays i))
    exact ⟨a.kernel,a.lengths,fun i _=> (a.pays i).trans_eq (scaledBills A i),fun i _=> le_add_of_nonneg_right (Real.log_nonneg (he i).2.1),fun i _ _ p=>(rootCost g p (he i).1 (he i).2.1).2⟩
lemma redeemBill {x z:ℝ}(h:exp (exp z) ≤ exp (exp (x-1))): z≤x:=by
    simp only [exp_le_exp] at h; linarith

theorem feasible_awards (g:G.Simple)(hA:LocalRatio Ñ)(pL:floors G p.kernel X≤ p.floorL)(a:Paid b' A)(hp:voucher W X Ñ ≤ Y.betaEntry)(hv:Tendsto X atTop atTop)(i:ℕ): ∀ᶠ ℓ :ℕ in atTop,∃ R:Realm G i Credit.leanC,R.draws=A ∧ R.paid=Ñ ∧ R.y=zz A ∧ R.anchor=ℓ :=by
    have he:Tendsto (fun i=> A.clock.J (i+1)) atTop atTop:= A.fits.deep.comp (tendsto_add_atTop_nat 1)
    obtain ⟨ℓ,hT⟩:= eventually_atTop.mp ((he.eventually_ge_atTop 5).and ((hv.comp he).eventually_ge_atTop i)); apply (eventually_ge_atTop ℓ).mono; intro j hj; obtain ⟨hx,H,⟨M⟩⟩:= install_awards g hA pL a hp j i (fun k hk=> hT k (hj.trans hk)); exact Aval M g hA hx H
end Ticket
end YM.WilsonCoeffUV.Bank
