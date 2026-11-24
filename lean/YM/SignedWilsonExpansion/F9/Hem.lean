import YM.SignedWilsonExpansion.F9.Title
/-! # Salary for high→pruned response and leading convergence at every cap/crop. -/
set_option autoImplicit false
set_option maxHeartbeats 175000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Wilson Gauge AnalyticNext.QuarticMatch.Sheets Filter Function Matrix Lattice RG Laurent Bloch Metric
open Blue FreeResolvent Work.F08 Bank Soil Exterior Next.Free Tree Precision Power Embroider
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb
open Realm Fountain PathCost Embroider.Canvas Shard PowerSeries XSpace
open Supply Ticket Polestar Next.Foundations Patrol Shard.Plan
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{A:Levels G}{Ñ:ChartRatio G}{J:Type*}{e k h m c v b N M j l r d p u n :ℕ}
variable {B Q D Z X Y η t a ρ:ℝ}{E W U V:Credit}{P:Era G ℝ}{R:Realm G (e+1) E}
local notation "κ'"=> ((n+1)*k)
variable {F:Frames G}{H:Hol G}{A':∀ h, Survey G H h}{K:∀ h,Rays G h H}
local notation "Rι"=> (F.level h)
namespace MarqueQ
namespace PorchK
open SignedWilsonExpansion.Commission Method Method.Epic Asymptotics Stair MergeTrip Looms Crops Taught
open Normalize (Sec)
open XSpace.Cirrus
variable {W':Initialize G}{Q':∀ h,Rays G h W'.hol}{Ω:Council F}
variable {P':Hol G}{ι:Type} {L:Filter ι}{Y θ μ ν η' :ι→ℝ}
variable (x:PorchK W' F Q' Ω R h k u)(q:ι→ PorchK W' F Q' Ω R h k u)(Wn:Normalize.Store G)
variable (St:∀ i≤e, Across L Y ℂ (fun j=>(q j).toEpic.tenor W' Wn i))(Bf:FrontQ q L Y θ μ ν)(pτ:ι→ℝ)(w:∀ᶠ i in L,0< θ i)(pt: TimeQ L θ pτ)
variable {S:SectionData (F.level d)} (hS:S.Sound P')(p0: Bid.pop S)(v₀:d≤h)
-- numerical frame ON appointed accounts, complex. Full-input cost, and *absolute* of higher weights. cap matrix for estimator branch sends field anywhere through cap.
variable {z:ι→(F.level d).Coeff}(p':SizeW L μ (F.level d) z)
local notation "μ₀"=> billSize
lemma gown_step (x:PorchK W' F Q' Ω R h k u) (n:ℕ)(y:(F.level d).Coeff)(t:ℝ):
     x.gown Wn n S t y=∑ j∈Finset.range (n+1),(t:ℂ)^j • account Wn x S y j:=by rw [atgown, citeS, LinearMap.sum_apply]; rfl
-- Fee Φ.Seen after clock.Append.Require.
include hS p0 v₀ w St Bf pt p'
lemma seen_step (T:Type)[AddCommGroup T][Module ℂ T](x: Sec G h→ₗ[ℂ] T){Z:ι→ℝ}(hn:n≤e)(hP:∀ i≤n, Salary L μ Z ℂ (fun i'=> x (account Wn (q i') S (z i') i))): Salary L μ Z ℂ (fun i=> x ((q i).gown Wn n S (pτ i) (z i))):=by
     simp_rw [gown_step,map_sum,map_smul x]; apply Salary.many Bf.inside_; intro i u; refine Salary.via (Salary.tilt (Wage.enroll (u:=μ) (clockQ.power (smallG q Bf) _ (TimeN w pτ pt) i 0 (Nat.zero_le _))) (hP i (Nat.le_of_lt_succ (Finset.mem_range.mp u)))) (.refl ..) (Eventually.of_forall fun i=> (?_)); change θ i^0* Z i=Z i; simp
lemma hewn_full (n:ℕ)(hn:n≤e): Salary L μ (fun i=>(q i).billSize d) ℂ (fun i=> (q i).gown Wn n S (pτ i) (z i)):= seen_step q Wn St Bf pτ w pt hS p0 v₀ p' (Sec G h) LinearMap.id hn (fun i p=> account_full q Wn hS p0 v₀ Bf St p' i (p.trans hn))
def bodyW (S:SectionData (F.level d)) (x:PorchK W' F Q' Ω R h k u)(K:ℕ)(pτ:ℝ)(z:(F.level d).Coeff): Sec G h:= Normalize.up v₀ (x.bodyD Wn K S pτ z)
lemma cloth_tithe (n:ℕ)(hn:n≤e):
    Salary L μ (fun i=> (q i).markW) ℂ (fun i=> (q i).gown Wn n S (pτ i) (z i)-bodyW Wn v₀ S (q i) n (pτ i) (z i)):=by
    let X(i):= (q i).gown Wn n S (pτ i) (z i); simp only [bodyW,bodyD,LinearMap.comp_apply]; simp_rw [regalia]; apply Salary.many Bf.inside_; intro i h'; have e':d < i.val:= ( Finset.mem_filter.mp h' ).2; have ht:=Nat.le_of_lt_succ i.isLt
    apply Salary.pass (P:=fun t=>Normalize.part h i (X t)) ( (?_) ) _
    have he:= seen_step q Wn St Bf pτ w pt hS p0 v₀ p' ( ↑(On.Grade G i.val) ) ( Normalize.part h i ) hn (fun j v=> account_bill q Wn hS p0 v₀ Bf St p' j i ht (v.trans hn)); refine Salary.transfer he (Wage.enroll (IsBigO.of_norm_le fun x=>?_)); let s:=(q x).markW; have hx:= (q x).mark_pos; change ‖(s^d)⁻¹*s^i.val‖ ≤ s; have hp':0<s:=hx; rw [Real.norm_of_nonneg ?_]; swap; · positivity
    have ht:s^i.val ≤ s^(d+1):= pow_le_pow_of_le_one hp'.le (q x).small e'; exact (mul_le_mul_of_nonneg_left ht (inv_nonneg.mpr (pow_nonneg hp'.le _))).trans_eq (by rw [pow_succ,←mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ hp'.ne'),one_mul])
variable {τh:ℕ}{Z:(F.level d).Coeff}(t_: Crest L Y ν η' (F.level d) z τh Z)
-- same basis β at higher (or own) rank converges from active Crest
include t_
lemma gown_tend (n:ℕ)(hn:n≤e)(β:(F.level h).Index)(v:τh≤wr Rι β)(p:wt Rι β=d):
    Tendsto (fun i=> sonar Rι β ((q i).gown Wn n S (pτ i) (z i))) L (𝓝 (sonar Rι β (Normalize.up v₀ (bulb G d ((F.level d).coords.symm Z))))) :=by
    let G₀:= sonar Rι β; let T' j i:= G₀ (account Wn (q i) S (z i) j); let X(i):= (pτ i:ℂ); let A:=G₀ (Normalize.up v₀ ( bulb G d ((F.level d).coords.symm Z))); let S':= ( Finset.range (n+1) ).erase 0
    have hu(i:ι): sonar Rι β ((q i).gown Wn n S (pτ i) (z i))=∑ j∈Finset.range (n+1),X i^j*T' j i:=by rw [gown_step Wn,map_sum]; exact Finset.sum_congr rfl (fun i _=>map_smul ..) -- explicit
    simp_rw [hu]
    have hx(i):∑ j∈Finset.range (n+1),X i^j*T' j i=T' 0 i+∑ j∈ S', X i^j*T' j i:= ( Finset.add_sum_erase (f:=fun j=> X i^j*T' j i) (Finset.range (n+1)) ( show 0 ∈ Finset.range (n+1) from (by simp)) ).symm.trans (by simp only [S',pow_zero,one_mul]); -- Finset.name order
    have he:Tendsto (fun i=>∑ j∈ S',X i^j*T' j i) L (𝓝 0):=by
       apply Wage.next_zero (Wage.sum Bf.inside_ _ _ (fun j h=> (?_))) Bf.decays
       have h0:= ( Finset.mem_erase.mp h ); have hu:=Finset.mem_range.mp h0.2; let P:= heady q Wn hS p0 v₀ Bf St β p' p j (show j≤e by have:=h0.1; omega); have he:= clockQ.power (smallG q Bf) X (TimeN w pτ pt) j 1 (Nat.pos_of_ne_zero h0.1); simp only [pow_one] at he; simpa only [mul_one] using Wage.mul (Wage.enroll (u:=μ) he) P
    simp_rw [hx]; simpa only [add_zero] using ( Tendsto.add ( launch_tend q Wn hS p0 v₀ Bf St (t':=p') β t_ p v ) he ) -- arg order
lemma body_poll (n:ℕ)(hn:n≤e)(β:(F.level d).Index)(v:τh ≤ wr (F.level d) β)(p:wt (F.level d) β=d):
    Tendsto (fun i=> sonar (F.level d) β ((q i).bodyD Wn n S (pτ i) (z i))) L (𝓝 (sonar (F.level d) β ( bulb G d ((F.level d).coords.symm Z)))) :=by
    let Y' i:=(q i).gown Wn n S (pτ i) (z i); let V:= upL F v₀ β; have hp :wt Rι V=d:= (congr_arg Prod.fst (up_grade F v₀ β)).trans p; have hx(i): sonar (F.level d) β ((q i).bodyD Wn n S (pτ i) (z i))=sonar Rι V (Y' i):=by rw [← breathe_up (d:=d) _ v₀ β]; change sonar Rι V (Normalize.up v₀ (PorchK.prune d h (Y' i))) = _; rw [assembleParts _ (Normalize.up _ _) hp, crown, ← assembleParts _ _ hp ]; exact le_rfl
    simp_rw [hx]; rw [← breathe_up (d:=d) _ v₀ β]; exact gown_tend q Wn St Bf pτ w pt hS p0 v₀ p' t_ n hn V (v.trans (congr_arg Prod.snd (up_grade F v₀ β)).symm.le) hp
end PorchK
end MarqueQ
end YM.WilsonCoeffUV.Mer.Xa
