import YM.WilsonCoeffUV.Product.Report.UVLimit
/-!
# Pre-block charges for multiple sectors
-/
set_option autoImplicit false
set_option maxHeartbeats 550000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Patrol
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Supply Ticket Polestar Next.Foundations Real Shard Plan
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n:Side}{U V:Type*}{r h D l e j k a N M m b i q z u:ℕ} {G:Gauge}{F:Labels.Frame G h}{H:Hol G}{A A':Levels G}

def prevec (G:Gauge)(I:Gear G)(k e u:ℕ):Prop:=∀ r, 0<r→ r≤ k+e→ pinCost u I r ≤ Real.exp (-Real.log I.patch.L.val/2)
lemma leave (p:0< r)(A:ℝ)(v:0≤A)(u:ℕ): ∀ᶠ L:ℕ in atTop, (A/L)^r*9^u ≤ Real.exp (-Real.log L/2):=by
    have he := logLane (A*(9:ℝ)^u)
    filter_upwards [he,tendsto_natCast_atTop_atTop.eventually_ge_atTop A,eventually_gt_atTop 0] with L h v' p'
    have hx:A/L≤ 1:= (div_le_one (by positivity)).mpr v'; rw [mul_div_right_comm A] at h; exact le_trans (mul_le_mul_of_nonneg_right (show (A/L)^r≤ A/L from (le_trans (pow_le_pow_of_le_one (by positivity) hx p) (le_of_eq (pow_one _)))) (by positivity)) h
lemma PreMark (Ñ:ChartRatio G)(K: KernelChoices)(k e u j:ℕ): ∀ᶠ L:ℕ in atTop,∀ (A:Levels G)(m:ℕ), A.clock.kernel=K → A.clock.J (m+1)= j → (A.S.block m).val=L →∀ (v:5≤ A.clock.J (m+1)) (x:ℕ)(p:craftQuest A m x v), prevec G (quest A m Ñ _ p).gear k e u:=by
    have hp i: ∀ᶠ L:ℕ in atTop,∀ (A:Levels G)(m:ℕ), A.clock.kernel=K → A.clock.J m=i → A.clock.J (m+1)= j → (A.S.block m).val=L →∀ (v:5≤ A.clock.J (m+1)) (x:ℕ)(p:craftQuest A m x v), prevec G (quest A m Ñ _ p).gear k e u:=by
       by_cases he:4≤ i∧5≤ j; swap; · exact Eventually.of_forall fun L A m _ h g _ b _ _=> False.elim (he ⟨h ▸ A.clock.adm _,g ▸ b⟩)
       let T:=cue G K i j he.1 he.2; let B:= tender (Hooks G) T.s u; let y:=T.preB*B; have hy:0≤y:=mul_nonneg T.pre_nn (tender_nn T.sigma ..)
       let S:= Finset.Ioc 0 (k+e); filter_upwards [(eventually_all_finset S).mpr (fun i h=> leave (Finset.mem_Ioc.mp h).1 y hy u)] with L v; intro A m f t z l v' a p r hp hv; have hx:= v r (Finset.mem_Ioc.mpr ⟨hp,hv⟩)
       subst K i j L; rw [pinCost, if_neg hp.ne',div_mul_eq_mul_div]; exact hx
    filter_upwards [(eventually_all_finset (Finset.range (j+1))).mpr (fun i _=> hp i)] with L v; intro A m b h; exact v (A.clock.J m) (Finset.mem_range.mpr (Nat.lt_succ_of_le (h ▸ A.fits.mono m.le_succ))) A m b rfl h
lemma PostHive (I:Gear G)(k e u b:ℕ) : ∀ᶠ z:ℝ in atTop, prevec G I k e u→ DormP I k e u z ∧ poreF G e k u b I≤ z:=by
    let X:=Finset.Iic e; let S:= Finset.Iic (k+e)
    filter_upwards [ (eventually_all_finset X).mpr (fun i _=> (eventually_all_finset S).mpr (fun r _=>eventually_ge_atTop (LowerF I k i r u))), (eventually_all_finset X).mpr (fun i _=> (eventually_all_finset S).mpr (fun r _=> eventually_ge_atTop (RoughF I k i r u))),eventually_ge_atTop (poreF G e k u b I)] with z h ht hv; exact fun t=>⟨⟨t,fun i r v q=> h _ (Finset.mem_Iic.mpr v) _ (Finset.mem_Iic.mpr q),fun i r v q=> ht _ (Finset.mem_Iic.mpr v) _ (Finset.mem_Iic.mpr q)⟩,hv⟩
lemma HiveSize (Ñ:ChartRatio G)(K:KernelChoices)(j e e' k u b:ℕ)(L:Side): ∀ᶠ Z:ℝ in atTop,∀ (A: Levels G)(m:ℕ), A.clock.kernel=K→ A.clock.J (m+1)=j → A.S.block m=L → ∀ (v:5≤ A.clock.J (m+1))(p:craftQuest A m e' v),let P:=(quest A m Ñ _ p).gear; prevec G P k e u→ DormP P k e u Z ∧ poreF G e k u b P≤Z:=by
    have hp i n: ∀ᶠ Z:ℝ in atTop,∀ (A:Levels G)(m:ℕ), A.clock.kernel=K → A.clock.J m=i → A.clock.J (m+1)=j → A.clock.J (m+2)=n → A.S.block m=L → ∀ (v:5≤ A.clock.J (m+1))(p:craftQuest A m e' v),let P:=(quest A m Ñ _ p).gear; prevec G P k e u→ DormP P k e u Z ∧ poreF G e k u b P≤Z:=by
       by_cases h : ∃ (A:Levels G)(m:ℕ), A.clock.kernel=K ∧ A.clock.J m=i ∧ A.clock.J (m+1)=j ∧ A.clock.J (m+2)=n∧ A.S.block m=L ∧ ∃ v:5≤A.clock.J (m+1),craftQuest A m e' v; swap; · refine Eventually.of_forall fun z A m b x v u y s k=>?_ ; exact False.elim (h ⟨A,m,b,x,v,u,y,s,k⟩)
       obtain ⟨A,m,u',h,h',t,pL,v,p⟩:= h; subst K i j n L
       let P:=(quest A m Ñ v p); filter_upwards [PostHive P.gear k e u b] with z hz; intro A' m' h h' u t v p' x
       have hh: (quest A' m' Ñ p' x).gear=P.gear:= by symm; apply twinning h h' u t v
       dsimp only; rw [hh]; exact hz
    let S:= Finset.Iic (j+1); filter_upwards [(eventually_all_finset S).mpr fun i _=> (eventually_all_finset S).mpr fun n _=>hp i n] with Z h; intro A m b v; let n:=A.clock.J; have hm:n m≤ n (m+1):=A.fits.mono m.le_succ; have ht:n (m+2)≤n (m+1)+1:= A.fits.stepSlow _; exact h _ (show n m∈ S from Finset.mem_Iic.mpr (by unfold n at *; omega)) _ (show n (m+2)∈ S from Finset.mem_Iic.mpr (by unfold n at *; omega)) A m b rfl v rfl
abbrev StageP (i:ℕ) :=Fin (i+1) × Fin (i+1) × Fin (i+1) × Fin (i+1)
private def StagePre (Ñ:ChartRatio G)(K:KernelChoices)(j i:ℕ)(a:StageP i):= (eventually_atTop.mp (PreMark Ñ K a.2.1 a.1 a.2.2.1 j)).choose
private def StagePost (Ñ:ChartRatio G)(K:KernelChoices)(j i:ℕ)(L:Side)(a:StageP i):= (eventually_atTop.mp (HiveSize Ñ K j a.1 i a.2.1 a.2.2.1 a.2.2.2 L)).choose

def preMark (Ñ:ChartRatio G)(K:KernelChoices)(j i:ℕ) :ℕ:=∑ a:StageP i,StagePre Ñ K j i a
def postMark (Ñ:ChartRatio G)(K:KernelChoices)(j i:ℕ)(L:Side): ℝ:= ∑ a:StageP i,Real.exp (Real.exp (StagePost Ñ K j i L a))
lemma handledCash (Ñ:ChartRatio G)(K:KernelChoices)(j i k u b e:ℕ)(A:Levels G)(m:ℕ)(p:A.clock.kernel=K)(v:A.clock.J (m+1)=j)(t: 5≤ A.clock.J (m+1))(x:craftQuest A m i t) (he:e≤ i)(hp:k≤ i)(hx:u≤ i)(hu:b≤ i)(g:preMark Ñ K j i≤ (A.S.block m).val){Z:ℝ}(z:postMark Ñ K j i (A.S.block m) ≤ exp (exp (Z-1))) : DormP (quest A m Ñ t x).gear k e u Z∧ poreF G e k u b (quest A m Ñ t x).gear ≤ Z:=by
     let a:StageP i:= (⟨e,by omega⟩,⟨k,by omega⟩,⟨u,by omega⟩,⟨b,by omega⟩)
     have hz:StagePre Ñ K j i a≤ (A.S.block m).val:= le_trans (Finset.single_le_sum (f:= StagePre Ñ K j i) (fun _ _=>Nat.zero_le (StagePre Ñ K j i _)) (Finset.mem_univ a)) g
     have ht: StagePost Ñ K j i (A.S.block m) a≤ Z:=redeemBill ((Finset.single_le_sum (f:=fun b=>exp (exp (StagePost Ñ K j i _ b))) (fun _ _=> (exp_pos _).le) (Finset.mem_univ a)).trans z)
     exact (eventually_atTop.mp (HiveSize Ñ K j e i k u b (A.S.block m))).choose_spec _ ht A m p v rfl t x ((eventually_atTop.mp (PreMark Ñ K k e u j)).choose_spec _ hz A m p v rfl t i x)
lemma handled (Ñ:ChartRatio G)(K:KernelChoices)(j i k u b e:ℕ)(A:Levels G)(m:ℕ)(p:A.clock.kernel=K)(v:A.clock.J (m+1)=j)(t: 5≤ A.clock.J (m+1))(x:craftQuest A m i t) (he:e≤ i)(hp:k≤ i)(hx:u≤ i)(hu:b≤ i)(g:preMark Ñ K j i≤ (A.S.block m).val)(z:postMark Ñ K j i (A.S.block m) ≤ A.clock.hatBeta m) : DormP (quest A m Ñ t x).gear k e u (zz A m)∧ poreF G e k u b (quest A m Ñ t x).gear ≤ zz A m:=by
    exact handledCash Ñ K j i k u b e A m p v t x he hp hx hu g (z.trans_eq (scaledBills A m))
end YM.WilsonCoeffUV.Mer.Patrol
