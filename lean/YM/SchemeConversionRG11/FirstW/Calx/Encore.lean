import YM.SchemeConversionRG11.FirstW.Calx.Feast
/-! Evaluate gradient sign and power. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function MeasureTheory Filter Set Metric Topology Lattice Pert Align Laurent Position Deck
open scoped BigOperators Classical ContDiff
variable {G:Gauge}{T:Itinerary}{F:Labels.Frames G}{c:ℕ→Side}
variable (T)
def pit (a:Who G 6)(i:ℕ):= tin G (T.period i) a
def owed (Q:Wash)(a b:Who G 6)(ε:Cover→ G.Color)(m:ℕ):= ∑ u:Ticket,∑ v:Ticket,expenditure T (oweX T Q a b ε u v) m
def transported (a b:Who G 6)(ε:Cover→ G.Color)(m:ℕ):= native a.val 0 (shiftT ε (pit T b m))
local notation "W" => (fun (t v:Ticket)=> icon (fresh t) (fresh v))
def softP (Q:Wash)(a b:Who G 6)(ε:Cover→ G.Color)(i:ℕ)(x:Cover):= tabL T Q i x*(∑ t:Ticket,∑ s:Ticket,inner ℝ (rail x (W t s) (pit T a i)) (rail x (W t s) (shiftT ε (pit T b i))))
lemma spends (Q:Wash)(a b:Who G 6)(ε:Cover→ G.Color): ∀ᶠ i in atTop, 8*transported T a b ε i= owed T Q a b ε i+∑ x∈pod T Q.rOut i,softP T Q a b ε i x := by
 have hp : Lives T Q.rOut (softP T Q a b ε) := Eventually.of_forall fun i x hi=>by by_contra h; unfold softP tabL at hi; rw [soft_life Q _ (lt_of_not_ge h).le,zero_mul] at hi; exact hi rfl
 let Z(i:ℕ):= pit T b i; let A(i:ℕ):=pit T a i
 filter_upwards [stackV T Q.rOut (softP T Q a b ε) hp, earn T a Q (fun i=>shiftT ε (Z i))] with i hi he
 rw [← hi, transported, ←he]; unfold expenditure owed; unfold expenditure -- maybe owed includes
 -- swap sum sites, simplify scar
 have eq : (∑ u:Ticket,∑ v:Ticket,∑ x:Site (T.period i),oweX T Q a b ε u v i (lift x)) = ∑ x:Site (T.period i),∑ u:Ticket,∑ v:Ticket,oweX T Q a b ε u v i (lift x) := by
    conv_lhs => arg 2; intro u; rw [Finset.sum_comm]
    rw [Finset.sum_comm] -- indentation
 rw [eq,←Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro x _; dsimp only [Z,A,softP]; simp_rw [Finset.mul_sum,←Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro u _; apply Finset.sum_congr rfl; intro v _; unfold oweX; simp only [pit, scar,inner_sub_right, real_inner_smul_right,tabL,sub_add_cancel]
lemma motion_cost (Q:Wash)(a b:Who G 6)(ε:Cover→ G.Color)(e:ε 0=0) : ∀ᶠ i in atTop,
 sectorA (tin G (T.period i)) 1 0 (wheelS G T i Q) a b (momentE ε) = (1/2)*(transported T b a ε i-transported T a b ε i) - (1/16)*(owed T Q a b ε i +owed T Q b a ε i) := by
 filter_upwards [spends T Q a b ε,spends T Q b a ε] with i h b'
 let L x:= (tin G (T.period i) x); let B:=wheelS G T i Q; let S:=pod T Q.rOut i
 have hp : B (L a) (L b) (momentE ε) = (1/48) * ((∑ x∈S,softP T Q a b ε i x)+(∑ x∈S,softP T Q b a ε i x)) := by
   unfold B; rw [wash_eq,← Finset.sum_add_distrib, Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; dsimp only [softP]; rw [←mul_add,← Finset.sum_add_distrib]; simp_rw [← Finset.sum_add_distrib,tower_shift,← Finset.mul_sum]; unfold pit L tabL; ring
 rw [sector_eq,show wheelS G T i Q _ _ _= _ from hp]
 rw [echoLeg,one_pow,inv_one,one_smul,contact_shear _ _ _ _ e]
 unfold S; unfold transported pit at *; linarith only [h,b']
variable {T}
lemma collectH {I E:Type*} [TopologicalSpace E] [AddCommGroup E] [ContinuousAdd E] (s:Finset I)(f:I→ℕ→E)(h:∀ i∈s,Helen (f i)):Helen (fun j=>∑ i∈s,f i j) := by
 induction s using Finset.induction with
 | empty=> simp only [Finset.sum_empty]; exact ⟨0,tendsto_const_nhds⟩
 | insert a s hh ih=> obtain ⟨v,hv⟩:=h a (Finset.mem_insert_self ..); obtain ⟨x,hx⟩:=ih (fun i hi=>h i (Finset.mem_insert_of_mem hi)); simp only [Finset.sum_insert hh]; exact ⟨_,hv.add hx⟩ -- ContinuousAdd extends ContinuousAddₗ? 
lemma owed_roll (hc:MarkGrid T c)(Q:Wash)(l:ℕ)(ε:Cover→ G.Color)(hε:ε∈Loft _ (l+1))(a b:Who G 6)(ha:fee a=2)(hb:fee b=2): Helen (fun i=> T.gap i^((l:ℤ)-3) * owed T Q a b ε i) := by
 simp_rw [owed,Finset.mul_sum]; apply collectH; intro w _; apply collectH; intro v _; simpa only [expenditure,Finset.mul_sum] using here_bill Q l ε hε a b ha hb hc w v -- missing arguments
private lemma costs_balance {I:Type*}[Fintype I] (A:I→I→I→ℂ)(e:∀ a b k,A a b k= -A b a k): ∑ a:I,∑ b:I,∑ c:I,A a b c=0 := by
 let f:=∑ a:I,∑ b:I,∑ k:I,A a b k; have hh:f= -f:= by
    unfold f; conv_lhs=> rw [Finset.sum_comm]
    simp_rw [←Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _; exact Finset.sum_congr rfl fun k _=>e b a k
 exact (mul_eq_zero.mp (show 2*f=0 from by rw [two_mul,← sub_neg_eq_add]; exact sub_eq_zero.mpr hh)).resolve_left (by norm_num)
lemma petty (F : Labels.Frames G) (ε:Cover→ G.Color)(B:Field4 G)(p:E F 6)(v:ℕ) :
 ∑ a:Who G 6,∑ b:Who G 6,∑ k:Who G 6, root3 (cloak F p) a b k * (↑((1/2:ℝ)*(transported T b a ε v-transported T a b ε v)*native k.val 0 B):ℂ)=0 := by
 let A (a b k:Who G 6):=root3 (cloak F p) a b k * (↑((1/2:ℝ)*(transported T b a ε v-transported T a b ε v)*native k.val 0 B):ℂ)
 have e(a b k:Who G 6): A a b k= - A b a k:=by unfold A; rw [root3,root3,commute (cloak F p) b a]; push_cast; ring
 exact costs_balance A e
lemma paid_grad (hc:MarkGrid T c)(Q:Wash)(p:E F 6)(l:ℕ)(ε:Cover→ G.Color)(hε:ε∈Loft _ (l+1))(hi:ε 0=0) (B:Field4 G): Helen (fun i=> T.gap i^((l:ℤ)-3) • dew T i Q p (momentE ε) B) := by
 let K (v:ℕ):= T.gap v ^ ((l:ℤ)-3)
 let f i a b k := root3 (cloak F p) a b k * (↑((1/16:ℝ)*(owed T Q a b ε i +owed T Q b a ε i)*native k.val 0 B):ℂ) -- k type inferred
 have ht (a b k:Who G 6): Helen (fun i=>K i • f i a b k):= by
    by_cases h: root3 (cloak F p) a b k=0
    · simp only [f,h,zero_mul,smul_zero]; exact ⟨_,tendsto_const_nhds⟩
    obtain ⟨_,hb,ha⟩:= top_six F p a b k h; obtain ⟨x,hx⟩:= owed_roll hc Q l ε hε a b ha hb; obtain ⟨y,hy⟩:=owed_roll hc Q l ε hε b a hb ha; have hp := ((((Complex.continuous_ofReal.continuousAt.tendsto.comp (hx.add hy)).const_mul (1/16:ℂ)).mul_const (↑(native k.val 0 B))).const_mul (root3 (cloak F p) a b k))
    refine ⟨_,hp.congr fun i=>?_⟩; dsimp only [comp_apply,f]; unfold K; rw [Complex.real_smul]; push_cast; ring
 let g:=fun i=>∑ a:Who G 6,∑ b:Who G 6,∑ k:Who G 6, f i a b k
 have he:Helen (fun i=>K i • g i):=by simp_rw [g,Finset.smul_sum]; apply collectH; intro a _; apply collectH; intro b _; apply collectH; intro k _; exact ht a b k
 obtain ⟨t,H⟩:= he; refine ⟨_,((H.const_mul (2:ℂ)⁻¹).neg).congr' ?_⟩
 filter_upwards [eventually_all.mpr (fun a=>eventually_all.mpr fun b=>motion_cost T Q a b ε hi)] with i hi
 rw [dew_val]; have hv:saleF T i Q p B (momentE ε) =0 := by simp_rw [saleF,burn_eq,letter_T]; simp
 have hh : saleF T i Q p (momentE ε) B = -g i:= by simp_rw [saleF,burn_eq, hi,sub_mul,Complex.ofReal_sub,mul_sub (α:=ℂ), Finset.sum_sub_distrib]; rw [petty (T:=T) F ε B p i,zero_sub]
 rw [hv,hh]; unfold K; simp [Complex.real_smul, mul_left_comm]
lemma kissed (hc:MarkGrid T c)(F:Labels.Frames G)(Q:Wash): kissC T (fun j=> bondM F T j Q):= by
 intro i hi q h hv
 obtain ⟨ε,hP,e,ht⟩:= primitive q.a.val q.i (cabin_stor q.e) hv
 by_cases hk:q.j=0
 · have hh:quietly q.b.val:= steady0 q.b (hk ▸ q.h); obtain ⟨δ,hδ,g,hg⟩:=primitive q.b.val 4 (cabin_stor q.b.property) hh; simp_rw [rate,LinearMap.coe_mk, AddHom.coe_mk,bond_paid,dew_val,saleF,burn_eq,←e,←g,letter_T]; refine ⟨0,by simp⟩
 have hs:= paid_grad hc Q q.p q.i ε ht hP q.b.val; obtain ⟨z,hz⟩:=hs; obtain ⟨v,hV⟩:= Nat.exists_eq_add_one.mpr (Nat.pos_of_ne_zero hk)
 refine ⟨_,((T.cutoff.pow v).smul hz).congr ?_⟩; intro j; rw [e,smul_smul,show rate q (bondM F T j Q)= dew T j Q q.p q.a.val q.b.val from bond_paid T j Q _ _ _]
 congr 1; rw [← zpow_natCast (T.gap j),← zpow_add₀ (T.positive _).ne',show (↑v:ℤ)+(↑q.i-3)= -((4-i:ℕ):ℤ) from by rw [Nat.cast_sub hi]; omega, zpow_neg,zpow_natCast]
end YM.RG11.FirstW
