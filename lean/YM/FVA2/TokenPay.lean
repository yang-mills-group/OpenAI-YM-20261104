import YM.FVA2.ComposeLog
/-!
# Additional uniqueness for the bare (a-*dependent*) field cost.
In addition to the unique L and Z, every TaylorOKM angular team yields the *same coupling and matrix D*. Uses comparison on increasing regulators. Not concluding non-growth of that matrix or syntactic equality of all terms of `Team`.
 -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
noncomputable section
namespace YM.FVA2.Erase
open Set Filter Function Finset MeasureTheory Pert Pert.Position Maxwell Maxwell.Free PositionX PositionX.Jet PositionX.Ribbon Topology Elegant Verne Counterpart Blaze Frost ColorCode
open MS MS.Land MS.Landau MS.Tide MS.Menus MS.Theater Lattice BoxOffice ArchTurn
open PositionX.Bend Prow PertExtension.LatticePT WorldJet
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}(V: Warehouse G){h:G.Simple}{B: Booked (wings G)}(M:MS_Data G B){p:ℝ}(R:Booth p V.F){s:ℝ}{n m d:ℕ}
variable (P:Land.Prescription (wings G))(HS: Blaze.ExactSpin V P)(HU:Frost.Trusted P) (H: MixedStory.AllProfiles M V P)
variable (Q: Land.Prescription (wings G))(S: ExactSpin V Q)(T: Trusted Q)(A: MixedStory.AllProfiles M V Q)
local notation "ℓ"=> V.F
local notation "Ω"=> sameAxis V.F d
variable {q:ℕ+}(hq:1<q.val)(K:Knocker h R q hq ( BoxOffice.warehouse V ))
open scoped Topology BigOperators ContDiff Classical
local notation "Fχ"=> Elegant.clockM P q 0
-- helper ν
private lemma top_sub {E:Type*}[NormedAddCommGroup E]{P Q:ℕ→E}{x:E}(h:Tendsto P atTop (𝓝 x))(ht:Tendsto Q atTop (𝓝 x)) : Tendsto (fun i=> P i-Q i) atTop (𝓝 0):= by simpa using! h.sub ht
include HS HU H hq
lemma ticking (d k:ℕ)(s:ℝ): Tendsto (fun i:ℕ=> bust h V P HS HU q s i d k ) atTop (𝓝 ( Elegant.turns h V M s d k )) := ( Prow.hugs ( fading q hq ) (( report_power h V P M HS HU H q hq s ( f:=id ) tendsto_id d k ).1) tendsto_const_nhds ) -- defeq λ
omit HS HU H hq
private lemma fame (x y:ℝ)(he:∀ (d:ℕ)(i:Owner G d)(j:BasisIx G d),(P.fees d i n).register j=( Q.fees d i n ).register j): bareD V P x y n d=bareD V Q x y n d:= by
    apply (Ω).ext; intro j; rw [D_pane,D_pane,loadAt,loadAt,Blaze.factory,Blaze.factory ]; apply congr_arg; apply Finset.sum_congr rfl; intro k _; congr 1; unfold rateV oil; rw [he _ j.2 ]
local notation "xP" i=> Elegant.clockM P q 0 i
include HS HU H S T A K hq
lemma prices_eq (n d:ℕ)(u: Owner G d) (p:BasisIx G d) : (P.fees d u n).register p=(Q.fees d u n).register p:= by
    induction n using Nat.strong_induction_on generalizing u d with| h n ih=>
       let x(i:ℕ):ℝ:= 0-Pond.clock q i; let W := E V.F d; let Y:= sameAxis V.F d; let a(i n):= bareD V P ( epsilon q i ) ( x i ) n d; let b(i n):= bareD V Q ( epsilon q i ) ( x i ) n d; apply planted V P _ n _ Q q hq; by_cases hn:n=0; · subst n; simp_rw [ solo V M P HS HU H _ _ _ ( epsilon_pos q _|>.ne' ),solo V M Q S T A _ _ _ (epsilon_pos q _|>.ne'),sub_self ]; simp
       let Y0 (i:ℕ):=dawnFrame V P HS HU q 0 i d; let C0(i:ℕ):=dawnFrame V Q S T q 0 i d; let Y1(i:ℕ):=bust h V P HS HU q 0 i d; let C1(i:ℕ):=bust h V Q S T q 0 i d;
       have hm : ∀ k<n,∀ t:ℕ,( Y0 t ) k=( C0 t ) k:= by
           intro k hp a; apply follows_right; change projectionD V P _ _ k _=projectionD V Q _ _ k _; rw [projectionD,projectionD,fame V P Q _ _ ( ih k hp ) ];
       have hK := fun k=> ticking (h:=h) V M Q S T A hq d k 0;
       have hu: ∀ᶠ i in atTop, luxury (Y0 i) (Y1 i)=luxury (C0 i) (C1 i):= by
           filter_upwards [trade h V P M HS HU H q hq 0 d, trade h V Q M S T A q hq 0 d] with i hm ht; unfold Y0 Y1 C0 C1; rw [ ← hm.1, ← ht.1 ]; unfold clockM ζq; rw [ Plot.clock_eq V M R P HS HU H hq K S T A ]
       have hx:=clean_ξ hu (Eventually.of_forall (fun i=> ⟨ motherZ V M P HS HU H _ _ (epsilon_pos q i|>.ne'),fun k hk=> hm k hk i⟩)) ( show n>0 from Nat.pos_of_ne_zero hn ) ( (by rw [← Elegant.reports0 h V M 0 d]; exact hK 0) : Tendsto (fun i=> C1 i 0) atTop (𝓝 0) ) (top_sub (E:= Buffer V.F d) (P:= fun i:ℕ=> C1 i n) (Q:= fun i:ℕ=> Y1 i n) (hK n) (ticking (h:=h) V M P HS HU H hq d n 0));
       let f:Buffer V.F d→ℂ:=fun t=> Y.coord p (t.val ( Y ( Land.read u ) )); have hp: ContinuousAt f 0 := by
            let T : E ℓ d →L[ℂ]ℂ:= LinearMap.toContinuousLinearMap (Y.coord p); exact T.continuous.continuousAt.comp ( ( Continuous.clm_apply ( show Continuous (fun p:Buffer ℓ d=>p.val) from continuous_subtype_val) ( show Continuous (fun _:Buffer ℓ d=> Y (Land.read u)) from continuous_const) ).continuousAt )
       have βv (i:ℕ) : ( a i n-b i n ) (Y ( Land.read u ))= ( (Y0 i n-C0 i n).val ) ( Y (Land.read u )):= by
           let v:= Y ( Land.read u ); change _= (a i n v - topD _ _ n v ) - (b i n v - topD _ _ n v); rw [LinearMap.sub_apply,sub_sub_sub_cancel_right ];
       simp_rw [ ← zero_sub ( Pond.clock q _ ) ]; rw [ ← show f 0=0 from map_zero ( Y.coord p ) ]; exact (hp.tendsto.comp hx).congr fun i=>congr_arg _ (βv i).symm
lemma field_eq (x y:ℝ)(n d:ℕ): bareD V P x y n d= bareD V Q x y n d:= fame V P Q x y (prices_eq V M R P HS HU H Q S T A hq K n)
-- all M with Pact (same Booked), Note suffices different data; use Tune unique along pointed.Arch.B.S. extension later.
end YM.FVA2.Erase
