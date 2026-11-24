import YM.UniformConstruction.ReadoutCompat.TarmacMonies
import YM.RG17.Rock

/-! Screen approximation points chosen, not restrict OPE matching to unfolded tails. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Filter Set Spec Table OPE OPE.Orbits SharpGram Trace Next.UVStress PhysicalNext PhysicalNext.Repeat.Legato Lattice RG Wilson Extraction Cells
open scoped Topology Classical BigOperators
variable {G:Gauge}(R:Run G){S:Table R.family.book}{f: Extraction.Order}{F: Final R.family f S}{B:Filter (ℕ×ℕ)}{L:Layout F} {s:Extraction.Sequence} (Z:Ledger L)(fx:Flick R.family.path.levels)
set_option quotPrecheck false
local notation "C"=> R.family
local notation "O"=> OPE.run
local notation "H"=> R.family.path.levels.clock.hatBeta
local notation "K"=> wheel R.family
local notation "a"=> R.family.S.a
local notation "t"=> (fun r=> H (K r))
local notation "o"=> (fun r=> r*t r)
include Z fx
variable {n:ℕ} (Y m:ℝ→ℕ) {x:Points n} {u:Filter ℝ} (b:ℝ→ Fin n→ Cover)
lemma mintConf (h:Lookup R m) (hi:u≤home) (hk:∀ᶠ r in home,Y r ≤ m r)(ht:Tendsto (fun r=>tag (role R.family r) (b r)) u (𝓝 x))(hx:x∈conf n) : ∀ᶠ r in u, Plot R.family (Y r) (m r) (K r) (b r):=by
   let v (i: Fin n)(r:ℝ):=tag (role R.family r) (b r) i
   have he (i:Fin n): Tendsto (v i) u (𝓝 (x i)):= (show Continuous (fun x: Points n=> x i) from by fun_prop).continuousAt.tendsto.comp ht
   have hh0:Tendsto t u atTop:= ((Next.Rank.Station.hat_rate _ Z.simple).comp (turnsWheel C)).mono_left hi
   have hV(i:Fin n): ∀ᶠ r in u, 8*‖v i r‖<t r:=(by obtain ⟨c,hc⟩:=exists_gt (8*‖x i‖); filter_upwards [((he i).norm.const_mul 8).eventually (gt_mem_nhds hc),hh0.eventually_ge_atTop c] with r h he; exact h.trans_le he) -- name
   let Y'(r):ℝ:= (R.family.path.levels.budget (K r)).B
   have hP : ∀ᶠ r in u,∀ i j:Fin n,i≠j → 2*(role R.family r * Y' r^2)< ‖v i r-v j r‖:=by
       refine eventually_all.mpr (fun i=> eventually_all.mpr (fun j=>?_))
       by_cases hq:i=j; exact Eventually.of_forall fun _ h=>(h hq).elim
       have hx': 2*(0:ℝ)<‖x i-x j‖:=by simpa only [mul_zero] using norm_sub_pos_iff.mpr ((show Injective x.ofLp from hx).ne hq)
       obtain ⟨p,hp,hQ⟩:= exists_between hx'; filter_upwards [((bendsPrice Z fx).mono_left hi|>.const_mul 2).eventually (gt_mem_nhds hp), (((he i).sub (he j)).norm).eventually (lt_mem_nhds hQ)] with i hi hp _; exact hi.trans hp
   filter_upwards [positiveLength.filter_mono hi,h.log.filter_mono hi,hk.filter_mono hi,eventually_all.mpr hV,hP] with r hr hV hk hz hP
   have he' (i: Fin n): R.family.S.gridPoint (wheel C r) (b r i) = r • v i r:=congr_arg (fun x:Points n=> x i) (scaledRole («C»:=R.family) hr (b r)).symm
   refine ⟨fun i=>?_,fun i j e=>?_,hk,hV.2.le⟩
   · rw [he',norm_smul,Real.norm_of_nonneg hr.le,mul_left_comm]; exact (mul_lt_mul_of_pos_left (hz i) hr).trans_le hV.1.1
   dsimp only [Function.comp_apply]; rw [he',he', ← smul_sub,norm_smul,Real.norm_of_nonneg hr.le]; exact (show (2*a _)*_=r*(2*(role C r*Y' r^2)) from by unfold role Y'; field_simp).trans_lt (mul_lt_mul_of_pos_left (hP i j e) hr) -- multiplication assoc
end YM.RG17
end

set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Filter Set Spec MeasureTheory OPE OPE.Orbits SharpGram Trace Next.UVStress PhysicalNext PhysicalNext.Repeat.Legato Lattice RG Wilson
open Extra.Multi FullVolume.Sever Marker Source Overlay PhysicalNext.Repeat.Mallow Bandage MergeProof MergeProof.Accent Ribbons ManyCopies Extra.Histories Extraction Word Next.Rank Station Edition Spindle Cells
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}(R:Run G){S:Table R.family.book}{f: Extraction.Order}{F: Spec.Final R.family f S}{B:Filter (ℕ×ℕ)}{L:Layout F} {D:Lenses.Mantle F B}{s:Extraction.Sequence}
    (Z:Ledger L)(fx:Flick R.family.path.levels)(W:Services R.family f S)
set_option quotPrecheck false
local notation "C"=> R.family
local notation "ι"=> R.family.path.levels
local notation "H"=> R.family.path.levels.clock.hatBeta
local notation "Q"=> wheel R.family
local notation "a"=> R.family.S.a
local notation "δ"=> renal R.family.path.levels
local notation "η"=> near R.family.path.levels
variable {n:ℕ} (J:Fin n) (d:Fin n→ℕ) (t l:ℕ) {α:ℝ} (Y m:ℝ→ℕ)
local notation "S'"=> R.family.path.levels.budget
local notation "e'"=> -((t+1/16:ℝ)*(1-α))
local notation "T"=> interval D s

-- NONE omitted at terminal physical regulator. Read early station u, not replacing any all-sector masked estimate on all configurations
open Push
variable {WLG:Bid.Worth} {rL:ℕ→ℕ} {doors} (g: Log.LogPackage R.family WLG rL doors)
open OPE.Log
include R Z fx J g
include W
variable {x:Points n}(b:ℝ→ Fin n → Cover)
lemma assuresConf (ho:Moored C L.level) (h:Lookup R m)(hp: Height R.family.S home OPE.run Y α) (hh:α<1) : ∃ q v:ℝ→ℝ, ValueStamp home OPE.run q ∧ RateLE home OPE.run v (-((t+1/16:ℝ)*(1-α))) ∧
   ∀ (x:Points n)(b:ℝ→ Fin n → Cover), x∈conf n → Tendsto (fun r=>tag (role R.family r) (b r)) home (𝓝 x) →
    ∀ᶠ r in home,∀ᶠ p:ℕ×ℕ in L.lens,∀ w:(i:Fin n)→ R.family.label (d i), (∀ i:Fin n,Paid L r w i ≤ (R.family.path.levels.clock.hatBeta (wheel R.family r))^l)→
     let o:= wrap (R.family.side (wheel R.family r) p.2) ∘ b r; let u(i):= atRef L (d i) r p (w i);
     ∃ z:R.family.label t,CollectionR R d t r p.1 p.2 o u (q r*R.family.S.a (m r)^t) (v r) (Y r) (m r) z:=by
   obtain ⟨l',hl⟩:= (eventually_all.mpr (fun j:Fin n=> eventually_ge_atTop (1+8*(d j+1)+l))).exists
   obtain ⟨q,v,hq,hv,hQ⟩:= allocatesG R Z fx J d t l' Y m g h hp hh
   refine ⟨q,v,hq,hv,fun x b he hT=>?_⟩
   have ht:home ≤ home:=le_rfl; have hz:= mintConf R Z fx Y m b h ht ((hp.earlier hh ageLarge h.spine).mono fun _ h=>h.le) hT he
   have ha:∀ᶠ r in home, R.family.S.a (L.level r) ≤ r:= Filter.Eventually.mono ho (fun i hi=>hi.1)
   filter_upwards [hz,hQ.filter_mono ht,(turnsWheel C|>.mono_left ht).eventually_ge_atTop 1,eventually_all.mpr (fun i=> (goingWheel R Z fx).grows.eventually_ge_atTop (R.family.ref (d i))|>.filter_mono ht),eventually_all.mpr (fun i=>Z.reach.growing.eventually_ge_atTop (R.family.ref (d i))|>.filter_mono ht),ha,(reverseSpoke C fx Z.simple).filter_mono ht] with r hr hp he hU hm ha hA
   let k:=Q r; let g:=Y r
   have hY:= (OPE.Cards.largeMesh f).mono_left L.certified
   filter_upwards [(large_mesh f (g)).filter_mono L.certified,(large_mesh f (k+1)).filter_mono L.certified,(large_mesh f (L.level r)).filter_mono L.certified, (late_period hr.marsh).filter_mono L.certified,hY.eventually (near_center C g t R.makes), eventually_all.mpr (fun i=> hY.eventually (near_center C g (d i) R.makes))] with p hg hk hM hN hT hS w hx o u
   have h':k<p.1:=hk; have hR :1 ≤ R.family.path.levels.clock.hatBeta k:= ((ι).fits.delayed k).le
   have hw (i):Spindle.paid R.family (d i) k p.1 p.2 (u i) ≤ R.family.path.levels.clock.hatBeta k^l':=by
       have hv: a (L.level r) / a k ≤ R.family.path.levels.clock.hatBeta k^8 := (div_le_iff₀ (R.family.S.a_pos _)).mpr ((ha.trans hA).trans_eq (mul_comm ..))
       have hs:= YM.RG17.ReadoutCompat.monies (p:=p.2) R fx L W (d i) 8 l k (L.level r) (w i) (r:=r) rfl he (hm i) (hU i) h'.le hM hv (hx i)
       exact ((le_mul_of_one_le_left (paid_pos ..) (col_ge C k)).trans (show moneys C (d i) k p.1 p.2 (u i) ≤ _ from hs)).trans (pow_le_pow_right₀ hR (hl i))
   have hF:Edition.Spaced (R.family.path.levels.budget k).B o∧ ∀ i,loops C k p.2 (o i) (m r+1)=0∧ R.family.S.place (o i)= R.family.S.gridPoint k (b r i) := hN
   exact hp p.1 p.2 h' hg o (fun i=>(hF.2 i).1) hF.1 u hw (fun i => hS i hg _ _ (by rw [R.family.S.embeds_place, (hF.2 i).2]; exact (hr.fit i).le.trans (R.family.S.strictAnti.antitone (hr.first.trans (Nat.le_succ _)))) _) (fun i=> hT hg p.2 _ (by rw [latzero]; simp [(R.family.S.a_pos _).le]) _)
end YM.RG17
end

set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Filter Set Spec MeasureTheory OPE OPE.Orbits OPE.Log Extraction Word
open Next.UVStress SharpGram PhysicalNext PhysicalNext.Repeat.Legato Lattice RG Wilson Next.Rank MergeProof Ribbons ManyCopies
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}(R:Run G){S:Table R.family.book}{f: Extraction.Order}{F: Spec.Final R.family f S}{B:Filter (ℕ×ℕ)}{L:Layout F} {D:Lenses.Mantle F B}{s:Extraction.Sequence}
    (Z:Ledger L)(fx:Flick R.family.path.levels)(W:Services R.family f S)
set_option quotPrecheck false
local notation "C"=> R.family
local notation "ι"=> R.family.path.levels
local notation "H"=> R.family.path.levels.clock.hatBeta
local notation "Q"=> wheel R.family
local notation "a"=> R.family.S.a
local notation "T"=>OPE.run
variable {n:ℕ} (d:Fin n→ℕ) (t:ℕ) (b:ℝ→ Fin n→ Cover)(Y m:ℝ→ℕ) {α:ℝ} (h:Lookup R m) (ho:Moored R.family L.level)
include W Z fx in
lemma buysSeen (hY:Height R.family.S home T Y α)(hh:α<1) {f₀:ℕ} {u:ℝ→(j:Fin n)→R.family.label (d j)} (j:Fin n) (he:∃ u r D,OPE.Log.LogPackage R.family u r D)(h:Lookup R m) (ho:Moored R.family L.level)(ha:∀ᶠ r in home,∀ i:Fin n,Paid L r (u r) i≤ H (Q r)^f₀) : ∃ q v:ℝ→ℝ,ValueStamp home T q ∧ RateLE home T v (-((t+1/16:ℝ)*(1-α)))∧ ∀ b:ℝ→ Fin n → Cover,∀ x:Points n,x∈conf n → Tendsto (fun r=>tag (role R.family r) (b r)) home (𝓝 x)→∀ᶠ r in home,∃ (y:ℕ×ℕ→R.family.label t) (X:R.family.label t) (p:Filter (ℕ×ℕ)), p.NeBot ∧ p≤L.lens∧ Tendsto y p (𝓝 X)∧ ∀ᶠ j in p, readingPrice R d L r (Y r) (m r) (q r) (v r) t (b r) (u r) j (y j):=by
    obtain ⟨f',ℓ,D',h'⟩:=he
    obtain ⟨q,v,hq,hV,hκ⟩:= assuresConf R Z fx W j d t f₀ Y m h' ho h hY hh
    refine ⟨q,v,hq,hV,fun b x hx hv=>?_⟩; filter_upwards [hκ x b hx hv,h.spine.grows.eventually_ge_atTop (R.family.ref t),ha] with r he hr ha using scenes R d t b (Y r) (m r) hr (u r) (q r) (v r) (he.mono fun i hi=> hi (u r) ha)
include W Z fx
lemma yieldsSeen (p:ℝ→ℝ)(M:ℝ→R.family.label t)(q:ℝ→ℝ) (v:ℝ→ (j:Fin n)→ R.family.label (d j)){α:ℝ}(h:Height R.family.S home T Y α)(ha:0<α)(hb:α<1){w:ℕ}(ht:∀ᶠ r in home,∀ i:Fin n,Paid L r (v r) i≤ H (Q r)^w) {x:Points n}(hr:Tendsto (fun r=>tag (role R.family r) (b r)) home (𝓝 x))(hx:x∈conf n)(hy:∀ᶠ i in home, Screen (R.family.S.gridPoint (wheel C i) ∘ b i)) (hL:Lookup R m) (hh:RateLE home T p (-((t+1/16:ℝ)*(1-α)))) (P:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (hX:∀ᶠ r in home,∃ (y:ℕ×ℕ→R.family.label t) (p':Filter (ℕ×ℕ)), p'.NeBot ∧ p'≤L.lens∧ Tendsto y p' (𝓝 (M r))∧ ∀ᶠ j in p', readingPrice R d L r (Y r) (m r) (q r) (p r) t (b r) (v r) j (y j)): RateLE home T (fun r=> P.packet t (R.family.S.gridPoint (wheel C r) ∘ b r) (d:=d) (fun i=>master L _ r (v r i)) 0 - S.project t (M r)) (-((t+1/16:ℝ)*(1-α))):=by
    have hV: GradePrice P d (fun r i=>master L _ r (v r i)) 0:=fun i j=>by
        let z(r):= L.shift (d i) r (v r i); apply (engineeringUpper P L Z.reach W (d i) j z ?_).mono
        · simp
        have hX:=runMount R Z fx; exact RateLE.of_norm_le (f:=fun r=> H (Q r)^w) (((hX.power w).pays ageLarge).mono (by norm_num)) (ht.mono (fun r hr=> (RG12.norm_le_mass ..).trans (hr i)))
    have hz : ∀ᶠ i in home,Dress («C»:=R.family) L.lens S (Y i) (m i) (Q i) (p i) (q i*a (m i)^t) (OPE.Orbits.names (S:=S) (d:=d) (fun j=>master L _ i (v i j))) (b i) t (M i):=by
       filter_upwards [hX,(eventually_all.mpr fun j=>Z.reach.growing.eventually_ge_atTop (R.family.ref (d j))), hL.spine.grows.eventually_ge_atTop (R.family.ref t)] with r hr he hP; obtain ⟨y,φ,hY,hφ,hQ,hU⟩:=hr; exact budgetDress R d (Y r) (m r) (q r) (p r) t (b r) (v r) y hφ hQ hU hP he
    apply (fines F W P Y m Q ha hb h (goingWheel R Z fx) L.certified _ b M hz hh ?_ hV ?_).mono ?_
    · exact hy
    · obtain ⟨a',ha',hA⟩:= Metric.nhds_basis_closedBall.mem_iff.mp ((conf_open n).mem_nhds hx) -- ha'
      obtain ⟨X,η,hX,hη,hκ⟩:= roomCosts (isCompact_closedBall x a') hA; refine ⟨X,η,hX,hη,?_⟩; filter_upwards [hr.eventually (Metric.closedBall_mem_nhds _ ha'),positiveLength] with i hi hv
      rw [show R.family.S.gridPoint (wheel C i) ∘ b i= posed i (tag (role C i) (b i)) from funext fun j=>congr_arg (fun x:Points n=> x j) (scaledRole hv (b i)).symm]; exact hκ _ hv _ hi
    exact max_le (by have h:0 ≤ (t:ℝ):= Nat.cast_nonneg _; nlinarith only [h,ha]) le_rfl
end YM.RG17
end

set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Filter Set Spec MeasureTheory OPE OPE.Orbits OPE.Log Polar Extraction Word Table Metric
open Lattice RG SharpGram PhysicalNext PhysicalNext.Repeat.Legato
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}{U:Spec.Final R.family f S}{L:Layout U}
variable {B:Filter (ℕ×ℕ)}{D:Lenses.Mantle U B}(Z:Ledger L)(W:Services R.family f S)(fx:Flick R.family.path.levels)(hz:Pegs D L) (P:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
set_option quotPrecheck false
local notation "T"=>OPE.run
local notation "C"=> R.family
local notation "H"=> R.family.path.levels.clock.hatBeta
variable {n:ℕ} (d: Fin n → ℕ)(t:ℕ) (v:ℝ→Labels S d) (p:GradePrice P d v 0)
    (A:Free R.family t→L[ℂ] ℂ) (u:ℝ→ℂ) (ht:RateLE home T u 0)
include p
private abbrev walkPath {n:ℕ} (X:ℝ → Fin n → E4) (M η:ℝ):= ∀ᶠ i in home,WithinRoom i M η (X i) 0
include p hz W ht
local notation "K"=> wheel R.family
local notation "R'"=> R.family.S.gridPoint
include fx
lemma heard_Any (p₀:Fin n) (g:ℝ→ (Fin n→E4)→ℂ) (X:ℝ→ Points n) {x:Points n}(hT:x ∈conf n)(hX:Tendsto X home (𝓝 x)) (Y:ℝ→ Fin n→ E4)(hY:Y=fun i=>posed i (X i)) (G':Loom g Y) (hg:∀ b:ℝ→ Fin n→ Cover,Tendsto (fun i=> tag (role C i) (b i)) home (𝓝 x)→ (∀ᶠ i in home,Screen (R.family.S.gridPoint (wheel C i) ∘ b i))→∃ C₀:ℝ, ∀ᶠ i in home, ‖u i * A (toFrame L t i (P.packet t (pix R b i) (v i) 0)) - g i (pix R b i)‖≤C₀) : ∃ C₀:ℝ, ∀ᶠ i in home, ‖u i * A (toFrame L t i (P.packet t (Y i) (v i) 0)) - g i (Y i)‖ ≤ C₀:=by
    obtain ⟨q,J,c,hc,hj⟩:= porch R W hz P d t v p A u ht
    obtain ⟨a,ha,hA⟩:= Metric.nhds_basis_closedBall.mem_iff.mp ((conf_open n).mem_nhds hT); obtain ⟨M,η,hM,hη,hκ⟩:= roomCosts (isCompact_closedBall x a) hA
    have hv:walkPath Y M η:=by filter_upwards [positiveLength,hX.eventually (closedBall_mem_nhds _ ha)] with i hi hx; rw [hY]; exact hκ _ hi _ hx
    let X':= centered Y id; let F₀ i x:= ∑ j,c j i*whole S x (v i) (bearing (J j)) (fields S (J j)); let f(i)(z):= F₀ i (X' i z) -g i (X' i z);
    let κ:ℝ:=2*((Fintype.card (Fin n×Axis):ℝ)+1); have HK:1≤κ:=by unfold κ; have hx: (Fintype.card (Fin n×Axis):ℝ)≥0:= Nat.cast_nonneg _; linarith
    let T' i:= 2*T i^2; have hI:∀ᶠ i in home,2 ≤ T i:=ageLarge.eventually_ge_atTop 2; have hm:∀ᶠ i in home,1 ≤ T' i:= hI.mono fun i hi=> by unfold T'; nlinarith only [hi]
    have ha:∀ᶠ i in home,∀ z∈closedBall (0:Fin n→ E4) 1,Watches (f i) z (T' i) κ:=by
       filter_upwards [meetSum (v:=v) (R:=c) U J tendsto_id hη (x:=Y) hv,G'.demands,listRates U J tendsto_id hη v (fun j=>⟨_,beforeFrame R P d v p j⟩) c (fun j=>⟨_,hc j⟩) (x:=Y) hv,hI] with i hG hD hz ht z hu; have hc := mem_closedBall_zero_iff.mp hu; obtain ⟨hh,hq⟩:= hD z hc; have h (j:Fin n)(a:Axis) : ∃ p:Ortho, ‖(forwards p).val-basis a‖< knobSize (Fin n) ∧ Radiates (f i) z (ray j p) (Real.exp (T' i)):=by
           obtain ⟨p,hp,hT⟩:=hz z hc j a; refine ⟨p,hp,?_⟩
           have hi : Real.exp (T i^2) + Real.exp (T i^2) ≤ Real.exp (T' i):=by
               unfold T'; rw [two_mul,Real.exp_add]; let e:=T i^2; have hx :2 ≤ Real.exp (T i^2):=by nlinarith only [ht,Real.add_one_le_exp (T i^2)]
               nlinarith only [hx]
           have hy:hT=hT:=rfl; unfold f X'; simp_rw [sub_eq_add_neg]; exact hT.add (by simpa only [norm_neg,norm_one,one_mul,neg_mul] using (hq j p).smul (-1))|>.mono hi
       obtain ⟨w,-,hp⟩:=h p₀ timeAxis; exact knobs_cost (f i) _ hp.at_center ((hG z hu).sub hh) h
    have hE:∃ A,∀ᶠ i in home,‖f i 0‖≤ A:=by
       apply Joint17.hike (X:= Fin n → E4) hm (Eventually.of_forall (fun i:ℝ=>HK)) ha; intro v' hv'; obtain ⟨y,b,hQ,hρ⟩:=Joint17.hopping W.simpleGate fx HK Y v' hv'; let U i:= tag (role R.family i) (b i); have hC: Tendsto U home (𝓝 x):=by
          let RV(i):= (run i)⁻¹ • y i; have hz:Tendsto RV home (𝓝 0):=by
             refine squeeze_zero_norm' ?_ (tendsto_inv_atTop_zero.comp ageLarge); filter_upwards [ageLarge.eventually_gt_atTop 0,hρ] with i hi hx; unfold RV; rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hi.le)]; exact mul_le_of_le_one_right (inv_nonneg.mpr hi.le) hx.2.1
          let Z' (v: Fin n → E4):= WithLp.toLp 2 v; have hz': Tendsto (fun i=> (Z' (RV i):Points n)) home (𝓝 0):=by
              apply ContinuousAt.tendsto (f:=fun i:Fin n→E4=>WithLp.toLp 2 i) (by fun_prop)|>.comp hz
          rw [← add_zero x]; refine (hX.add hz').congr' ?_; filter_upwards [positiveLength,hρ] with i hp hh
          apply MulAction.injective₀ hp.ne'; unfold U; dsimp only; rw [smul_add,scaledRole hp]; ext1 j; change (posed i (X i)) j+ i • (Z' (RV i):Points n) j= (R.family.S.gridPoint (wheel R.family i) ∘ b i) j; rw [← hh.2.2]; unfold centered; change (posed i (X i)) j+i • ((run i)⁻¹ • (y i j))= Y i j+(i/run i) • (y i j); rw [smul_smul,hY,div_eq_mul_inv]
       obtain ⟨A',hA⟩:=hg b hC (Eventually.of_forall hQ); have hΓ: RateLE home T (fun i=>u i * A (toFrame L t i (P.packet t (pix R b i) (v i) 0))- F₀ i (pix R b i)) (-1):= by
          apply hj; refine ⟨M+η,η/2,add_nonneg hM hη.le,half_pos hη,?_⟩; filter_upwards [within_centered tendsto_id hη (X:=Y) hv,hρ] with i hi he; unfold pix; rw [← he.2.2]; exact hi (y i) he.2.1
       refine ⟨1+A',y,?_,hρ.mono fun i hi=> hi.1⟩; filter_upwards [hρ,hA,(RateIs.const ageLarge one_pos).outweigh hΓ neg_one_lt_zero ageLarge] with i hi hA hE; unfold f X'; rw [hi.2.2]; exact (norm_sub_le_norm_sub_add_norm_sub _ (u i * A (toFrame L t i (P.packet t (pix R b i) (v i) 0))) _).trans (add_le_add ((norm_sub_rev ..).le.trans hE) hA) -- name
    obtain ⟨c₁,hC⟩:=hE; refine ⟨1+c₁,?_⟩; filter_upwards [hC,(RateIs.const ageLarge one_pos).outweigh (hj Y ⟨_,_,hM,hη,hv⟩) neg_one_lt_zero ageLarge] with i hC hE; unfold f X' centered at hC; simp only [smul_zero,add_zero] at hC; exact (norm_sub_le_norm_sub_add_norm_sub _ (F₀ i (Y i)) _).trans (add_le_add hE hC)
end YM.RG17
end

set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Filter Set Spec MeasureTheory OPE OPE.Orbits OPE.Log Polar Extraction Word Table Metric
open Lattice RG SharpGram PhysicalNext PhysicalNext.Repeat.Legato
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}{U:Spec.Final R.family f S}{L:Layout U}
variable {B:Filter (ℕ×ℕ)}{D:Lenses.Mantle U B}(Z:Ledger L)(W:Services R.family f S)(fx:Flick R.family.path.levels)(hz:Pegs D L) (P:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
set_option quotPrecheck false
local notation "T"=>OPE.run
local notation "C"=> R.family
local notation "H"=> R.family.path.levels.clock.hatBeta
variable {n:ℕ} (d: Fin n → ℕ)(t:ℕ) (v:ℝ→Labels S d) (p:GradePrice P d v 0)
    (A:Free R.family t→L[ℂ] ℂ) (u:ℝ→ℂ) (ht:RateLE home T u 0)
local notation "Q"=> wheel R.family
include fx Z W hz
lemma clearOrder (m:ℝ→ℕ)(h:Lookup R m)(ho:Moored R.family L.level) (Hb:∃ u r D,OPE.Log.LogPackage R.family u r D)(j:Fin n) {v:ℝ→(i:Fin n)→R.family.label (d i)} {i:ℕ} (ht:∀ᶠ r in home,∀ j:Fin n,Paid L r (v r) j≤ H (Q r)^i) :
     ∃ (α:ℝ)(Y:ℝ→ℕ)(q A₀:ℝ→ℝ), 0 < α ∧ α<1 ∧ Height R.family.S home T Y α ∧ ValueStamp home T q ∧ RateLE home T A₀ (-((t+1/16:ℝ)*(1-α))) ∧ ∀ x:Points n,x∈conf n→
        (∀ b:ℝ→ Fin n→ Cover,Tendsto (fun i=> tag (role C i) (b i)) home (𝓝 x)→∃ X:ℝ→R.family.label t,∀ᶠ r in home,∃ (p':Filter (ℕ×ℕ))(y:ℕ×ℕ→ R.family.label t),p'.NeBot∧p'≤ L.lens∧Tendsto y p' (𝓝 (X r))∧∀ᶠ j in p',readingPrice R d L r (Y r) (m r) (q r) (A₀ r) t (b r) (v r) j (y j)) ∧
        ∀ (Y':ℝ→ Points n),Tendsto Y' home (𝓝 x) → ∀ A:Free R.family t→L[ℂ] ℂ,∀ (f':ℝ→(Fin n→ E4) →ℂ) (N l:ℕ), let c:= fun r=> Z.g r^N*Z.Λ r^l
                                                                                         ; let z:= fun i=> posed i (Y' i)
                                                                                         ; Loom (fun i y=> (c i:ℂ)⁻¹ * f' i y) z →
           (∀ b:ℝ→Fin n → Cover,Tendsto (fun i=> tag (role C i) (b i)) home (𝓝 x) → (∀ᶠ i in home,Screen (R.family.S.gridPoint (wheel C i) ∘ b i)) → ∃ (X:ℝ→ R.family.label t), (∀ᶠ r in home, ∃ (p':Filter (ℕ×ℕ))(y:ℕ×ℕ→ R.family.label t),p'.NeBot∧p'≤ L.lens∧Tendsto y p' (𝓝 (X r))∧∀ᶠ j in p',readingPrice R d L r (Y r) (m r) (q r) (A₀ r) t (b r) (v r) j (y j)) ∧ ∃ M:ℝ,∀ᶠ i in home, ‖A (toFrame L t i (S.project t (X i))) - f' i (pix R b i)‖≤ M*c i) →
          ∃ M,∀ᶠ i in home, ‖A (toFrame L t i (P.packet t (z i) (d:=d) (fun j=> master L _ i (v i j)) 0))-f' i (z i)‖ ≤ M*c i:=by
    -- redo rate not dependent P choices
    let α:ℝ:= 1/(32*t+2); have ha:0<α:=by unfold α; positivity
    have he:0<(32:ℝ)*t+2:=by positivity
    have hβ:α<1:=by
         unfold α; have hh: (0:ℝ)≤t:=Nat.cast_nonneg t; exact (div_lt_one he).2 (by linarith only [hh])
    obtain ⟨Y,hY⟩:= found ageLarge R.family.path.levels.fits.mesh ha.le
    obtain ⟨q,a,hq,hA,hW⟩:= buysSeen R Z fx W d t Y _ hY hβ j Hb h ho ht
    have hv:GradePrice P d (fun r i=>master L _ r (v r i)) 0:=fun j k=>by
        let z(r):= L.shift (d j) r (v r j); apply (engineeringUpper P L Z.reach W (d j) k z ?_).mono
        · simp
        have hX:=runMount R Z fx; exact RateLE.of_norm_le (f:=fun r=> H (Q r)^i) (((hX.power i).pays ageLarge).mono (by norm_num)) (ht.mono (fun r hr=> (RG12.norm_le_mass ..).trans (hr j)))
    refine ⟨α,Y,q,a,ha,hβ,hY,hq,hA,fun x hx=> ⟨fun b hb=>?_,?_⟩⟩
    · have he:= hW b x hx hb; rw [eventually_iff_exists_mem] at he; obtain ⟨K,hK,hk⟩:=he; choose! y V hv using hk; exact ⟨V, mem_of_superset hK fun r hr=>by obtain ⟨p,hV,hz,hy,hU⟩:=hv r hr; exact ⟨p,y r,hV,hz,hy,hU⟩⟩
    intro X hX A f N l c Y' hg hp
    have hΛ(i):1≤Z.Λ i:= Z.above i; have hc(i):0 < c i:= mul_pos (pow_pos (Z.positive _) _) (pow_pos (zero_lt_one.trans_le (hΛ _)) _)
    let u:= fun r=> (c r:ℂ)⁻¹; have h(i) (x:ℂ): ‖u i*x‖= ‖x‖/c i:=by unfold u; rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg (hc i|>.le),div_eq_mul_inv,mul_comm]
    have hC:RateLE home T u 0:=by
        have he(i): ‖u i‖≤ ((Z.g i)^N)⁻¹:=by nth_rw 1 [← mul_one (u i),h,norm_one]; rw [one_div]; exact inv_anti₀ (pow_pos (Z.positive _) _) (le_mul_of_one_le_right (pow_nonneg (Z.positive _|>.le) _) (one_le_pow₀ (hΛ i)))
        apply ((Z.coarse_g.power N).inv.pays ageLarge).of_norm_le (Eventually.of_forall he)|>.mono
        simp
    obtain ⟨M,hM⟩:= heard_Any R W fx hz P d t _ hv A u hC j (fun i y=>u i*f i y) X hx hX Y' rfl hg (fun b hb hv'=> by
         obtain ⟨X,hX,M,hM⟩:=hp b hb hv'
         have he':= beacon R W t hz (yieldsSeen R Z fx W d t b Y m a X q v hY ha hβ ht hb hx hv' ‹Lookup R m› hA P (hX.mono fun i hi=>by obtain ⟨p,y,hp⟩:=hi; exact ⟨y,p,hp⟩))
         let f'(i):= u i * A (toFrame L t i (P.packet t (pix R b i) (d:=d) (fun j=> master L _ i (v i j)) 0-S.project t (X i)))
         letI:FiniteDimensional ℝ (Free C t):=Module.Finite.trans ℂ _
         have hv:RateLE home T f' (-(1/32)):= ((hC.mul (pay_fixed ageLarge ((A.restrictScalars ℝ).toLinearMap) he')).mono (le_of_eq (by rw [zero_add]; unfold α; field_simp; ring)))
         refine ⟨1+M,?_⟩; filter_upwards [hM,(RateIs.const ageLarge one_pos).outweigh hv (by norm_num) ageLarge] with i hi hh
         unfold f' at hh; rw [map_sub,map_sub,mul_sub] at hh
         refine (norm_sub_le_norm_sub_add_norm_sub _ (u i*A (toFrame L t i (S.project t _))) _).trans (add_le_add hh ?_); rw [← mul_sub,h]; exact (div_le_iff₀ (hc i)).mpr hi)
    refine ⟨M,hM.mono fun i hi=>?_⟩; rw [← mul_sub,h] at hi; exact (div_le_iff₀ (hc i)).mp hi
end YM.RG17
end
