import YM.SchemeRG11.Outer.Spin
/-! System of first-order estimates on cover, before H-average.
 -/
noncomputable section
set_option autoImplicit false
namespace YM.SchemeRG11.Dock
open Function Filter Asymptotics Topology MeasureTheory Metric
open Flock Lattice Pert Align Full Maxwell Haze Pile Catch World Atoll Tree Acorn Outlook Banner
open Labels Long MvPolynomial Air North Wolt Sew
open scoped Classical Pointwise
variable {I:Type}{G:Gauge}{n m:ℕ}{T: Align.Itinerary}
local notation "D₁"=> Atoll.land G
variable [DecidableEq I](s:Finset I)(p:I→ pLabel G)(t:Landmarks I) {R r:ℝ} (B:Window)
variable {F:Frames G}
lemma smoother(o:I)(ho:o∈s)(i:ℕ)(d:Dab n F)(R:ℝ)(h:IsWeightedHomogeneous generation (p o) n):
 markC s p t o T d i - (∑ j:Axis,∑ k:Axis,nearTag s p B t T o j k R i) =
 (D₁).avg ((D₁).neg.heat (Dab.tile T d (p o) R B i)*aerial (s.erase o) (fun l=>castZero (T.gap i) (p l)) (fun l=>motionP t o l i)) - (∑ j:Axis,∑ k:Axis,(T.gap i)^4 * ∑ x∈gateY T R i,cove T B i x*inside0 (s.erase o) (motionP t o) p (p o) T j k i x):=by
 rw [evaporation s p t o h,area s p t o ho h,mapC s p t o h ho]
 unfold Dab.tile crestF nebula; simp only [map_smul,map_sub,map_add,Dose.opposite, sub_mul, smul_mul_assoc,add_mul,smul_eq_mul]; ring
structure Fare (T:Align.Itinerary)(p:pLabel G)(d:Dab n F)(B:Window)(r R:ℝ): Prop where
 gate : Gate (D₁) Sew.Home (Brows T R) (Dab.tile T d p r B)
 bound (a): Tendsto (fun i=> T.gap i*d.M i a) atTop (𝓝 0)
omit [DecidableEq I] in
lemma supplier {q:pLabel G}(h:IsWeightedHomogeneous generation q n)(hp:B.rOut<r)(hv:r<R)(ht:Neutral q) : ∃ d:Dab n F,Fare T q d B r R:=by obtain ⟨m,q,A,a,b⟩:= shift_in h ht hp hv (T:=T) (F:=F); exact ⟨⟨m,q,A⟩,b,a⟩ -- q binder
lemma harbour {z:I→E4}(d:Dab n F)(o:I)(ho:o∈s)(h:Footpath T t s z)(he:Spaced R z s)(hb:B.rOut<r)(hr:r<R)(hp:IsWeightedHomogeneous generation (p o) n)(hd:Fare T (p o) d B r R):
 Finishes (fun i=>markC s p t o T d i-∑ j:Axis,∑ k:Axis,nearTag s p B t T o j k r i):=by
 let f:=motionP t o; let g(j):= z j-z o
 let u:=s.erase o; have ht:Footpath T f u g:=fun i p => (h _ (Finset.mem_of_mem_erase p)).sub (h _ ho)
 have hx:Spaced r g u:=fun i a j b hi=>by unfold g; rw [sub_sub_sub_cancel_right]; linarith only [he _ (Finset.mem_of_mem_erase a) _ (Finset.mem_of_mem_erase b) hi,hr]
 have hv(a:I)(w:a∈u): 4*R< ‖g a‖:= he a (Finset.mem_of_mem_erase w) o ho (Finset.ne_of_mem_erase w)
 have hR:= B.rOut_pos.trans hb
 simp_rw [smoother s p t B o ho _ d r hp]; apply Finishes.sub (lights u f g ht (hx.distinct hR) (fun i p=>by linarith only [hv i p,hr,hR]) p hd.gate)
 apply Finishes.sum _ _; intro j _; apply Finishes.sum _ _; intro k _; exact gleams u f p _ B ht hx hb (fun i p=>by linarith only [hv i p,hr,hR]) j k
variable [Fintype I]
lemma correctAll {z:I→E4}{k:I→ℕ}(h:Footpath T t s z)(he:Spaced R z s)(hb:B.rOut<r)(hr:r<R)(hp:∀i∈s,IsWeightedHomogeneous generation (p i) (k i)) (d:(i:I)→Dab (k i) F)(hv:∀i∈s,Fare T (p i) (d i) B r R):
 Finishes (fun i=> firstCovers s p (T.gap i) (fun l=> t l i)-∑ o∈s,∑ l:Fin (d o).m,Dab.rangeV T (d o) i l* coverGod s (Function.update p o ((d o).A l).p) (T.gap i) (fun l=> t l i)):=by
 let u(k:ℕ)(i j:Axis):=turnup s (fun l=>castZero (T.gap k) (p l)) (fun a=>t a k) i j
 have he1(i j:Axis):Finishes (fun k=> ∑' x:Cover,rest T B s t k x * u k i j x) := hilly s t p B h he (hb.trans hr) i j
 have ht(i:I)(hi:i∈s):=harbour s p t B (d i) i hi h he hb hr (hp _ hi) (hv _ hi)
 have H := (Finishes.sum s _ ht).sub (Finishes.sum Finset.univ _ (fun i _=>Finishes.sum Finset.univ _ (fun j _=> he1 i j)))
 apply H.same; filter_upwards [ eventually_all_finset (I:=Finset.univ) |>.mpr (fun (i:Axis×Axis) _=> packs s p B t T i.1 i.2 hb)] with i hi
 have hr(j k: Axis): (∑' x,u i j k x)=(∑' x, rest T B s t i x*u i j k x)+∑ o∈s,nearTag s p B t T o j k r i:= hi (j,k) (Finset.mem_univ _)
 unfold Acorn.firstCovers; simp only [markC]; unfold u at *; simp only [hr,Finset.sum_add_distrib, Finset.sum_sub_distrib]
 have hw : (∑ j:Axis,∑k:Axis,∑o∈s,nearTag s p B t T o j k r i)=∑o∈s,∑j:Axis,∑k:Axis,nearTag s p B t T o j k r i:=by rw [Finset.sum_comm (s:=s)]; apply Finset.sum_congr rfl;intro u _; rw [Finset.sum_comm]
 rw [hw]; ring
end YM.SchemeRG11.Dock
