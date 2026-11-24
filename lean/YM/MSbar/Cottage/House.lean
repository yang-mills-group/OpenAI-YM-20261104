import YM.MSbar.Cottage.Copy
import YM.MSbar.Cottage.Draw
import YM.MSbar.Atlas.Result
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Heath.Cottage
open Lattice Wilson RG Function Filter MeasureTheory Push.Local Push Push.AbsoluteSums WilsonStartup Bulk
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{c f:Side}{S:StepData c f} {U:Config G f}{R: Rep G f}{σ C T H K A B a v δ w β:ℝ}
open Finset RG.PathData Tree Push.Uniform Pressure
variable (F:Forest S.ratio) (X Y:Support f)
open AnalyticBridge.VerifiedReset Next.Scheduling Precision Stock
variable (J:Voice G) (Q:Config G c) (μ:Positions (Key F G)) (k:F.Free)
set_option quotPrecheck false
local notation "I!"=> IV F (board F X) G
local notation "U!"=> Config G f
local notation "Q!"=> twirl F (board F X)
local notation "o!"=> fence F (board F X) G
-- fields centered. Define individual A

def basin (Q:Config G c)(μ:Positions (Key F G))(k:F.Free)(h:ℝ) :=
   {U:Config G f | G.lieExp (fareX F J Q U k) = flume F Q U k ∧
        ∀ j:G.ColorIndex, |fareX F J Q U k j - μ (k,j)| ≤ h}
def basis (Q:Config G c)(μ:Positions (Key F G))(E:Finset F.Free)(h:ℝ) := 
   {U:Config G f| ∀ k∈E, U∈ basin F J Q μ k h}
-- enlarge I margin > Ω donor. Exterior good separately.
def hotel (Q:Config G c)(μ:Positions (Key F G))(a b:ℝ) :=basis F J Q μ (board F X) b ∩ basis F J Q μ (board F Y\board F X) a
local notation "H!"=> hotel F X Y J Q μ A B
variable (g:Clear G J)(b:ℝ)(k:F.Free)
include g
lemma portico (h:k∈board F Y) :Seal S (youth F Y) (basin F J Q μ k b):=by
    let z(U:U!):=flume F Q U k; let e(U:U!):= fareX F J Q U k; have he: Continuous z:= Continuous.mul ((continuous_apply k.val).comp (canoe_cont F)) continuous_const; have hg:Measurable e:=g.reads.comp he.measurable
    refine ⟨?_,?_,?_⟩
    · refine MeasurableSet.inter (measurableSet_eq_fun ((show Continuous G.lieExp by fun_prop).measurable.comp hg) he.measurable) ?_
      change MeasurableSet {U:Config G f | ∀ j:G.ColorIndex, abs (e U j-μ (k,j)) ≤ b}; simp_rw [Set.setOf_forall]; apply MeasurableSet.iInter; intro j
      have hh:Measurable fun i=>|e i j-μ (k,j)| := ((((EuclideanSpace.proj (𝕜:=ℝ) j).continuous.measurable.comp hg).sub measurable_const).abs)
      exact measurableSet_le hh measurable_const
    · simp only [Sweet,basin,Set.mem_setOf_eq,fareX,flume]; intro q h W; rw [grove F _ _ h]
    intro U V hU; simp only [basin, Set.mem_setOf_eq,fareX,flume]; rw [turnbook F hU k.val ((mem_filter.mp h).2)]
lemma supportK (b:ℝ) (E:Finset F.Free)(h:E⊆board F Y) : Seal S (youth F Y) (basis F J Q μ E b):=by
    induction E using Finset.induction_on with
    | empty=> rw [show basis F J Q μ ∅ b=Set.univ by simp [basis]]; exact ⟨MeasurableSet.univ,fun i he U=> by simp,fun U V he=> rfl⟩
    | @insert i E hh ih=> rw [show basis F J Q μ (insert i E) b= (basin F J Q μ i b) ∩(basis F J Q μ E b) by ext; simp [basis]]; exact (portico F Y J Q μ g b i (h (mem_insert_self ..))).combine (ih ((subset_insert _ _).trans h))
variable (ht:X⊆ Y)
include ht
lemma garden_main : Seal S (youth F Y) H!:= by
    have ht' : board F X⊆ board F Y:= fun i he=> mem_filter.mpr ⟨mem_univ _,ht ((mem_filter.mp he).2)⟩; exact (supportK F Y J Q μ g B (board F X) ht').combine (supportK F Y J Q μ g A _ sdiff_subset)
lemma blanks (t:I!)(z:F.Free)(hv:pegged F (board F X) t z≠ (1:G.El)):z∈board F X:=by by_contra hh; exact hv (dif_neg hh)
lemma hedge (t:I!):Booking (youth F Y) F (pegged F _ t):=⟨fun i hp=>by have hi:i.val.1∈Y:=ht ((mem_filter.mp (blanks F X Y J g ht t i hp)).2); exact ⟨halo_subset _ _ hi,page F (halo_subset _ _ hi)⟩⟩ -- page wants i.val.1∈ halo?
lemma safezone (t:I!): Q! t U∈basis F J Q μ (board F Y\board F X) a ↔ U∈basis F J Q μ (board F Y\board F X) a:= by
   have he(i:F.Free)(hx:i∈board F Y\board F X):flume F Q (Q! t U) i=flume F Q U i:=by unfold twirl flume; rw [stationary,show pegged F _ t i=1 from dif_neg (mem_sdiff.mp hx).2,one_mul]
   have hf(i:F.Free)(h:i∈board F Y\board F X): Q! t U∈ basin F J Q μ i a ↔ U∈basin F J Q μ i a:= by unfold basin; simp only [Set.mem_setOf_eq,fareX, he i h]
   exact ⟨fun p i h=> (hf i h).1 (p i h),fun p i h=> (hf i h).2 (p i h)⟩
-- extension.Forest fixed draped around P*. Add mean at every undetermined location to match view. absolute board.
def rented (Q:Config G c)(μ:Positions (Key F G))(U:Config G f): Positions (Key F G):= (tint G _).symm (fun i=>if i∈board F Y then fareX F J Q U i else (tint G _ μ) i)
def chambers (Q:Config G c)(μ:Positions (Key F G))(U:Config G f) := lifting F Q (tint G _ (rented F Y J Q μ U))
local notation "d!"=> chambers F Y J Q μ
include g
lemma informed : Measurable d! ∧ (∀ U:Config G f,canoe (S:=S) F U=d! U → True) ∧ LocalOn (youth F Y : Support f) d! :=by
    let u(i) (U:Config G f):= if i∈board F Y then fareX F J Q U i else tint G _ μ i; have he(U): d! U=lifting F Q (fun i=> u i U):=by unfold u chambers rented; rw [ContinuousLinearEquiv.apply_symm_apply]
    have hv(i:F.Free): Measurable (u i):=by by_cases h:i∈board F Y; unfold u; simp only [if_pos h]; exact g.reads.comp ((Continuous.mul ((continuous_apply _).comp (canoe_cont F)) continuous_const|>.measurable)); unfold u; simp only [if_neg h]; exact measurable_const
    have hh(U W : Config G f)(hp:Agrees (youth F Y) U W): (fun i=>u i U)=(fun i=>u i W):= by
      funext i; unfold u; split; next h=> unfold fareX flume; rw [turnbook F hp i.val ((mem_filter.mp h).2)]
      next h=> rfl
    refine ⟨?_,fun _ _=>trivial,fun U V hp=> (he U).trans ((congr_arg _ (hh U V hp)).trans (he V).symm)⟩
    rw [funext he]; apply Measurable.comp (g:=lifting F Q) _ (measurable_pi_lambda _ hv); apply Continuous.measurable; unfold lifting; fun_prop
lemma invites (i : Site f→G.El)(h:∀ x,i (S.ratio.embed x)=1) (U:Config G f): d! (Lattice.gauge i U)=d! U:=by unfold chambers rented fareX flume; rw [grove F _ _ h]
lemma boarding (hU:U∈H!)(hc:A≤B)(i:F.Free)(hz:i∈board F Y):U∈ basin F J Q μ i B:=by
   by_cases hh:i∈board F X; exact hU.1 i hh
   have hx:= hU.2 i (mem_sdiff.mpr ⟨hz,hh⟩); exact ⟨hx.1,fun k=> (hx.2 k).trans hc⟩
lemma cognizant (hU:U∈H!)(hc:A≤B) : Agrees Y (canoe (S:=S) F U) (chambers F Y J Q μ U):=by
   intro e he hv; unfold chambers lifting; by_cases h:e∈F.trunks; exact (F.compress U _ h).trans (F.on_tree _ ⟨e,h⟩).symm
   let i:F.Free:=⟨e,h⟩; have hh : i∈board F Y:= mem_filter.mpr ⟨mem_univ _,he⟩; have hp:= boarding F X Y J Q μ g ht hU hc i hh
   change _= F.drape _ i.val; rw [F.off_tree]; simp only [rented,ContinuousLinearEquiv.apply_symm_apply, if_pos hh]; rw [hp.1]; unfold flume; simp [i] -- hp type
lemma unfoldR (U:U!)(t:I!) : Spine X (canoe (S:=S) F U) (canoe (S:=S) F (Q! t U)) ∧ Spine X (d! U) (d! (Q! t U)):=by
   have hx i (h:i∈ board F Y)(hh:i∉board F X): fareX F J Q (Q! t U) i=fareX F J Q U i:=by unfold fareX flume twirl; rw [stationary, show pegged F _ t i=1 from dif_neg hh,one_mul]
   refine ⟨(winding (Y:=X) F J Q _ (fun i hv=> (mem_filter.mp (blanks F X Y J g ht t i hv)).2) Y U).1, spine_in (fun i hp=>?_)⟩
   unfold chambers lifting; by_cases hv:i∈ F.trunks; exact (F.on_tree _ ⟨i,hv⟩).trans (F.on_tree _ ⟨i,hv⟩).symm
   let j:F.Free:=⟨i,hv⟩; change F.drape _ j.val= F.drape _ j.val
   simp_rw [F.off_tree,rented,ContinuousLinearEquiv.apply_symm_apply]; by_cases ha:j∈board F Y; rw [if_pos ha,if_pos ha,hx j ha (fun hh=>hp ((mem_filter.mp hh).2))]; simp [ha]
-- norm uses coordinates.in receipt. cheap pledge uniform
lemma leanOn (hU:U∈H!)(hc:A≤ B)(hb:0≤ B): ‖rented F Y J Q μ U-μ‖ ≤ B:=by
   refine (pi_norm_le_iff_of_nonneg hb).mpr fun i=>?_
   change |tint G _ (rented F Y J Q μ U) i.1 i.2 - tint G _ μ i.fst i.snd| ≤ B; rw [rented, ContinuousLinearEquiv.apply_symm_apply]; dsimp only; split
   next hp => exact (boarding F X Y J Q μ g ht hU hc _ hp).2 _
   rw [sub_self,abs_zero]; exact hb
end YM.MSbar.Heath.Cottage
