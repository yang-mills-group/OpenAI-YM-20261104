import YM.Contacts.Revest.Anthem
/-! # Retune at actual bolt with explicit K table unchanged. For starting aux epoch.
 -/
noncomputable section
set_option autoImplicit false
namespace YM.Contacts.Revest
open AnalyticBridge VerifiedReset Collection Flute Outlay
open PhysicalNext.Repeat PhysicalNext.Repeat.Roost Terrain
open Function Filter Set Lattice Wilson RG Ovens Ovens.Pipes Quotes Residual WilsonStartup UVNext.PricedKernels Averaging Geo Progress.DirectedRecipe Extra.Iteration Org
open UVNext.CouplingReset Push.AbsoluteSums Animals Precision RG.Supply Input RG.Shoot PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Next.Scheduling PhysicalNext.ThroughLaunch Time Model Arbor Province.Costing Tucks Milling.Steam Pressure
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{l q r v t d D' μ s:ℝ}
namespace Anthem
section fire
open Mallow Spring Push.PriceCompiler
variable {M:Metals G}{D:Rolls M.p}{B:Alloy M D}{A:Factor B}{m n k i N:ℕ}
local notation "E" => B.B.a.params m
local notation "P" => B.B.a.budget m
local notation "N'" => B.B.a.clock.J m
local notation "n'" => B.B.a.clock.J (m+1)
local notation "x" => B.B.a.clock.hatBeta m
local notation "Y" => B.B.a.S.side m n
local notation "θ" => B.B.a.clock.allowance m
local notation "R" => B.B.kin.path N m
local notation "α" => B.B.kin.alpha N m
-- easier header.B
variable (g:G.Simple) {F:bore G} (hk:∀ i'≤k,Charted G k (B.B.a.clock.hatBeta m) (B.B.a.budget m) (B.B.kin.path N m) F (B.B.a.params m).clip d (ripe (B.B.a.clock.hatBeta m)) ε₀ i' i)
    (hu:Anthem.Steady G (B.B.a.params m) (B.B.a.clock.hatBeta m) d k i)
    (hB: Bargain G (B.B.a.params m) (A.book (B.B.a.clock.J (m+1)) (B.B.a.clock.J m)) (A.scout (B.B.a.clock.J (m+1)) (B.B.a.clock.J m)) (B.B.a.clock.hatBeta m) (B.B.a.clock.hatBeta (m+1)) (UVNext.CouplingReset.alphaBound D (B.B.a.clock.J (m+1))))
    (hw:10*(B.B.a.budget m).B < (B.B.a.S.side m n).val) (hm:m<N)
    {Q:UVNext.CouplingReset.In B.B.a m n} (H: Spring A N m n l q Q) (hr:r∈Set.Icc l q)
local notation "u" => (H.result r)

-- at padded E model(s). Keep predecessor link & projection delta and K schedules exactly. need not rewrite output at previous predecessor. proof no spare_num collisions.
include g hk hu hB hw hm H hr
lemma tryOn (hv:(u).beta∈band B.B.a m):∃ C:Rep G Y, B.B.Move N m n C (Q r) ∧ C.beta=(u).beta∧ C.eval=(u).eval∧ C.activities.K=(u).activities.K ∧ C.activities.forced=(u).activities.forced ∧ C.v=(u).v ∧ Truth C k F θ θ:= by
   let C:= (u); let X:= H.X'; let V:= H.V' r; let y:= Q r; let c:=shelves X R P; let z:=Collection.branch X R (E).clip P V α; let p:= P; let δ:= delta (X.read V); let a:= y.beta+α+δ; let w:= vac V (H.τ r); let W:= B.B;
   have h:C=finish R (E).clip P c z a w:= H.owns g hm hr; have hz:C.beta=a:= h ▸ (show _ from rfl); obtain ⟨hT,hS⟩:=H.knows r hr; have hP:= (A.machine.passes hm H.knows).1;
   let g₀:= ν x; let s := Time.fraction B.B.a m; have hy:0≤θ:=by change 0≤δE x; unfold δE Clock.gap; positivity
   let f:= integrated (n:=Y) p F (E).clip R k a; have hv':a∈ Icc ((1/4:ℝ)*x) (4*x):= by unfold band at hv; change C.beta ∈ Icc _ _ at hv; obtain ⟨hp,hv⟩:=hz ▸ hv; have hx:=hB.sound; constructor <;> linarith
   have hK:Flute.Salary p f g₀:= hu _ _ _ _ (show Time.Same (E) P from ⟨rfl,rfl,rfl⟩) hw hk a hv' a hv'|>.1; have hw:0≤g₀:=by have hx:=hB.sound; unfold g₀ ν; positivity
   let X':=Flute.put c p; let t:=Flute.lay (-f) z; let p':=Flute.put X' p; let C':= finish R (E).clip P p' (Flute.lay f t) a w; let ω':=quoteHard B.B.a m A.book y.beta;
   have h₁:Ingredients c z p s ω':=(H.core hm r hr).renew g (W.support.cap _ _ hm.le) hP.decent hP.width α (Return.enough_room B.B m n) (hP.fees r hr)
   have hV := Flute.height (Tucks.debt hK g₀ hw le_rfl) h₁; have hW:= Flute.height hK hV;
   have hM := H.moves g hm|>.2 r hr|>.1; let Y':=H.result r;
   have hx:C'.eval=C.eval:= by
       rw [h]; funext V; unfold C' p' X' t; rw [hW.unshifted, Flute.covers hV, Flute.covers h₁,h₁.unshifted]; have hp: film p (-f) V= -film p f V:= by unfold film; rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro i _; unfold masked Set.indicator; split_ifs <;> simp
       erw [hp,neg_neg, mul_assoc (Progress.DirectedRecipe.trunk ..|>.eval V) (Real.exp _) (Real.exp _), Real.exp_neg, mul_inv_cancel₀ (Real.exp_pos _).ne',mul_one]; rfl
   have hcap: (C'.activities).K=C.activities.K:= by rw [h]; rfl -- parentheses
   have htop: C'.activities.forced=C.activities.forced:= by rw [h]; rfl
   have he': |a-y.beta-α|≤1:= by rw [←hz]; exact hM.δ
   have he:g₀+(g₀+s)≤θ/24:= by rw [show g₀+(g₀+s)=δE x/32+2*g₀ from (by unfold s fraction; change g₀+(g₀+ δE x/32)=_; ring)]; exact hB.boot -- typo equality
   let Z:= C.activities; have hQ' := A.machine.coverage _ _ (Push.PriceCompiler.step_paid B.B.a m); have hh :=Time.now (Q:=Q) B.B hm A.machine.shops hQ'.1 (by rw [params_eq B.B.valid]; exact hQ'.2) A.exchange A.machine.cubic (s':=Set.Icc l q) (fun t ht=> (H.knows _ ht).2) |>.2 r hr -- arg
   obtain ⟨r',hv⟩:= hB.offer (A.exchange n' N') (B.B.a.clock.theta n') (B.B.a.S.block m).val (Nat.cast_pos.mpr (B.B.a.S.block m).pos) y.beta (trial_in hS)
   have hbill: θ /24 ≤ Echarge A.exchange A.book B.B.a m y.beta:= (r'.trans hv).trans_eq (by simp only [Echarge]; rw [Deployment.clock_eqns B.B.a.clock m|>.2.2.2.2.2.2]; rfl)
   have hγ:(P).threshold^2*|a-y.beta-α|≤portion A.exchange A.book B.B.a m y.beta:= le_trans ?_ hh.1; swap; · rw [← hz, ← sub_add_eq_sub_sub]; exact (show _ from (H.moves g hm|>.2 r hr|>.2.2.1))
   refine ⟨C', Purity.pours A hm hS hW hT (hx.trans hM.ident) he' ?_ (he.trans hbill) hγ, hz.symm,hx,hcap,htop,?_,?_⟩
   · have hq {v:ℝ} : Z.KBound p v→ C'.activities.KBound p v := by
         unfold Activities.KBound; rw [htop,hcap]; exact id
     have ht:= hW.gates R (E).clip a w; have hP₀:C.p=p:= h ▸ rfl; have hc :=hP₀ ▸ (show C.activities.Valid C.p θ (B.B.a.clock.forcedAllowance m) from (hM.bundle).valid.labels); change C'.activities.Valid .. ∧ C'.activities.KBound ..
     exact ⟨{ht with boundE:= E_rises ht.boundE (he.trans (by linarith only [hy])),boundK:=hq hc.boundK},hq (hP₀ ▸ hM.forced)⟩ -- Record
   · change C'.v=C.v; rw [h]; rfl
   let L:=solo R (E).clip p X' t f a w; have ht:=trumpet R (E).clip p X' t f hK a w hV; have hf:= Flute.lights R (E).clip p X' t f a w; obtain ⟨x₀,hc,hf',hv⟩:=ht.wage; exact ⟨L,⟨x₀,hc,fun i=>Cost.enlarge (hf' i) (he.trans (by linarith only [hy])),fun i=>Cost.enlarge (hv i) (by linarith only [he,hy,hw])⟩,hf⟩
-- at Nest
omit H hr
lemma pleats {U:Bolt B} (h: Graces.Nest A U) : let W:= U.history N n m; ∃ P': Rep G Y, B.B.Move N m n P' (U.history N n (m+1))∧Truth P' k F θ θ ∧ P'.beta=W.beta∧ P'.eval=W.eval∧P'.activities.K=W.activities.K∧ P'.activities.forced=W.activities.forced∧P'.v=W.v := by
   intro W; have hh:W.beta∈band B.B.a m:=(U.sticks _ _|>.prices m (Nat.zero_le _) hm.le).2; obtain ⟨l,t,Q,H,z,hz,hv,hc⟩:= (h.held N m n hm).1; have he:W=H.result z:=hc; obtain ⟨C,hQ,hβ,hV,hK,hF,hZ,h⟩:=tryOn (H:=H) g hk hu hB hw hm hz (he ▸ hh); exact ⟨C,hv ▸ hQ,h,he ▸ hβ,he ▸ hV,he ▸ hK,he ▸ hF,he ▸ hZ⟩
end fire
end Anthem
end YM.Contacts.Revest
