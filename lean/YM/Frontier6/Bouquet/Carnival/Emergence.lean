import YM.Frontier6.Bouquet.Carnival.Memory
/-! One-field markets. This includes the empty family. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet.Atelier
open Function Set Finset Ensemble MeasureTheory Normal Filter Road Forest Tale Spec Curtains Prescription Metric Audit Submodule Fareway
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff Matrix.Norms.Frobenius
open scoped YM.Frontier6.Bouquet
variable {I J L Y: Type}{G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable [NormedAddCommGroup Y][NormedSpace ℂ Y][NormedSpace ℝ Y][IsScalarTower ℝ ℂ Y][CompleteSpace Y]
variable (K:Final C F S){P Q:Ensemble}(d:Slot →ℕ)(v:(j:Slot)→ S.Field (d j))(i:P) (M:Pod→ℝ) (R: Air (S:=S) P I L Y)
def solitary (P:Ensemble):Prop:=∀ i:P,i.val.card=1
variable (h:solitary P)
include h
lemma Solitary.terminal (he: Q ≤ P): Q=P:=by
    have hv(p:Q): p.val=(assign he p).val:= by rcases (inside he p).eq_or_lt with hh|hh; exact hh; exact False.elim ((Nat.not_lt_of_ge (show 1 ≤ p.val.card from p.val.card_pos)) ((h (assign he p)) ▸ Pod.lt_card hh)) -- type order
    exact injective_assign he (fun p q hp=> Subtype.ext ((hv p).trans ((congr_arg Subtype.val hp).trans (hv q).symm)))
lemma Solitary.dimension : dim (fiber P)=0:=by
    have he:= fiber_dim P; have hv:= rank_split P; have hp:Fintype.card P=P.choose.card:= Fintype.card_coe ..; unfold solitary at h; simp only [h, Finset.sum_const, Finset.card_univ,nsmul_eq_mul,hp,Nat.cast_id,mul_one] at hv; omega -- inspect
lemma Solitary.price (i:P): difference i.val d= -(d i.val.here:ℝ):=by unfold difference; rw [normal_rank,h i]; rw [Pod.arityD, show i.val.val={i.val.here} from congr_arg Subtype.val (Pod.seed_of_one (h i)),sum_singleton]; simp
omit h
def invoiceP (x:Seats P)(i:P): Spelling S:= Tale.suit K (x i) (d i.val.here) (v i.val.here)
include h
lemma Solitary.mode (s a:ℝ)(x:Seats P)(H:Patron S P Y)(f:Full (fiber P)): uKernel K d v s a P x H f = f 0 • H (invoiceP K d v x):=by
   let T:=common a; have ht(q:Down P): q=lonely P:= Subtype.ext (Solitary.terminal h q.property); letI : Unique (Down P):= ⟨⟨lonely P⟩,ht⟩; unfold uKernel regulator; rw [Fintype.sum_unique]; let A:= prepared K T d v s; let U:=seedT d v; change branch K A T (le_refl P) x H f=_; rw [turns K T (le_refl P) (A:=A) (B:=U) (fun j hj=>oldest K T d v s j (h ⟨j,hj⟩))];
   letI : Unique (Trip (seedT d v) P):= inferInstanceAs (Unique (P→ Unit)); unfold branch; rw [Fintype.sum_unique,root_stamp, show costsD U (default:Trip (seedT d v) P)=0 from Finset.sum_eq_zero (fun _ _=>rfl), trains_zero]; rfl
abbrev balanceP (j:I):= R.sky j (invoiceP K d v (R.region j).center) -- included h? not used
lemma Solitary.pricePoint (he:R.Welkin M)(hp:Air.Hosts K R)(ε:ℝ)(hε:0<ε):∃ D:ℝ,0 ≤ D∧∀ j:I, ‖balanceP K d v R j‖ ≤ D*R.freight d j ε:=by
   let t:= R.lengths; let A(j:I):= stars d P (t j); let r:= R.account; let F(i:I):= (A i)⁻¹ • (r i)⁻¹ • balanceP K d v R i; have hC : ∃ D:ℝ,0≤ D ∧∀ i:I,‖F i‖ ≤ D*R.route.ruin i ε:= by
       refine R.route.told F (fun X f T hT x hX=>?_) ε hε; let u(i:P):=x (R.role i); let v':= fun i:P=>fun j:X=> invoiceP K d v (R.region (f j)).center i; let w(i:P):= (d i.val.here:ℝ)*u i
       have hZ : T.Mint (A ∘ f) (∑ i:P,w i):= Mint.mass Finset.univ (fun j:P=>fun k=> (t (f k) j)^ (difference j.val d)) w (fun j _=> ((hX (R.role j)).powers _).eq (by rw [Solitary.price d h j]; unfold w u; ring)) -- arg order
       let V:= insert (0:ℝ) (Finset.univ.image u); have hu(i:P):u i∈ V:= mem_insert_of_mem (mem_image_of_mem u (mem_univ i)); have hy:T.Costs (fun k=>(r (f k))⁻¹ • balanceP K d v R (f k)) (∑ i:P,w i):= hp X f T V x hX (mem_insert_self ..) (fun j hj=> by rcases mem_insert.mp hj with h|h; rw [h]; obtain ⟨j,_,rfl⟩:= mem_image.mp h; exact R.route.speaks_nonneg T f hX _) hu w v' (fun i=> by unfold w; rw [← zero_add ((d i.val.here:ℝ)*u i)]; exact Pen.suits K _ (Fareway.Costs.const (v _)) (Eventually.of_forall fun k=> (he.safe _).around i))
       have ht:=hy.scalarR₀ (hZ.inv.pay); rw [neg_add_cancel] at ht; exact ht
   obtain ⟨D,hD,hB⟩:= hC; refine ⟨D,hD,fun j:I=>?_⟩; unfold Air.freight; let a:= R.route.ruin j ε; let b:= balanceP K d v R j; have hb:= hB j; have ha:0<A j:= stars_pos d P _ (R.length_pos _); have hr:0<r j:=he.pos j
   change ‖b‖ ≤ D * (r j * A j * a); unfold F at hb; rw [smul_smul, norm_smul, Real.norm_of_nonneg (show 0 ≤ (A j)⁻¹ * (r j)⁻¹ from by positivity), ← mul_inv_rev,← div_eq_inv_mul, div_le_iff₀ (mul_pos hr ha)] at hb; exact hb.trans_eq (by unfold a; ring) -- b defin
lemma Solitary.launch : Sails K d v P 0:=by
   intro Y I L _ _ _ _ _ M R ht he hp B C ε hB hC hε; obtain ⟨D,hD,h⟩:= Solitary.pricePoint K d v M R h he hp ε hε -- h name now shadow; needed original rename
   refine ⟨D,hD,fun i A s a f hb hh hV hv=>?_,fun i A s a b f ha hb hh hV hv=>?_⟩ -- typo `D` endows existential tuple
   · rw [Solitary.mode K d v ‹solitary P›,norm_smul]; exact (mul_le_mul (Bouquet.Checks.sup f _ hv.costs 0) (h i) (norm_nonneg _) hv.costs.nonneg).trans_eq (by unfold Air.freight; ring)
   rw [Solitary.mode K d v ‹solitary P›,Solitary.mode K d v ‹solitary P›,sub_self,norm_zero]; apply le_trans _ (le_of_eq (show D*A*R.freight d i ε*R.delta i b = _ from ?_)); exacts [mul_nonneg (mul_nonneg (mul_nonneg hD hv.costs.nonneg) (R.freight_pos d he _ _).le) (R.delta_pos _ (ha.trans_le hb)).le, by unfold Air.freight Air.delta; ring]
omit h
lemma rank_descends (H: Q<P): dim (fiber Q)<dim (fiber P):=by have h:= rank H; have hv:= fiber_dim P; have hi:=fiber_dim Q; rw [ref_slots H.le] at hi; omega
lemma sails (P:Ensemble): ∃ n,Sails K d v P n:= by
   induction P using (measure (fun P=> dim (fiber P))).wf.induction with
   | h P ih=>
      by_cases he:solitary P; · exact ⟨0,Solitary.launch K d v he⟩
      obtain ⟨i,hi⟩:= not_forall.mp he; obtain ⟨n,h⟩:= seated K d v i (fun q h=> ih q (rank_descends h)); exact joins K d v i h (by have :=i.val.card_pos; omega)
-- every root ann
lemma pavilion : ∃ n, Seated K d v i n:= seated K d v i (fun q _=> sails K d v q)
end YM.Frontier6.Bouquet.Atelier
