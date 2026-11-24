import YM.OPE.Compatible.Speke.Poll
/-!
# Cubic scene. exactly one omitted root
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Nestle
open Function MeasureTheory Set Topology Metric Filter Lattice Laurent Flume Sagebrush Maxwell Extra.FD SphereTest Analysis
open scoped BigOperators Classical ContDiff
open Balsam Port Extra.FD.OPE
variable {U:Gloam}{r s:ℝ}{K:ℕ→ℕ}{u n:Side}{J:Zem}{k m:ℕ}
def localS {T:Type*}(X:Axis→Site n→T)(p:Site n)(a b:Axis):Fin 4→T:=![X a p,X b (p+step a), X a (p+step b),X b p]
abbrev cup (X:Candidate U)(p:Site (U.M k))(a b:Axis):Tile:=localS (fun i=>X i k) p a b
abbrev mx (X Y Z:Candidate U)(J:Zem)(a b)(i:ℕ)(z:Site (U.M i)):= voice (cup X z a b) * J (cup Y z a b) (cup Z z a b)
def hash (X Y Z:Candidate U)(J:Zem):ℕ→ℝ:=∑ v:PlaqAxes, (fun i=>∑ z:Site (U.M i), mx X Y Z J v.val.1 v.val.2 i z)
lemma cup_crystal (X:Candidate U)(z:Crew U)(p: Cover)(i:ℕ)(a b):cup X (rumB z i p) a b=yard (fun k=>peekX z X k i) p a b:=by
    have he(a: Axis): rumB z i p+step a=rumB z i (p-step a):=by unfold rumB;rw [map_sub,wrap_step]; abel
    funext x; fin_cases x
    · rfl
    · exact congr_arg (X b i) (he a)
    · exact congr_arg (X a i) (he b)
    rfl
lemma mx_pole (hs:Crown U K)(x:Crew U)(p:Pose)(a b l) : ∃ C≥0,∀ᶠ i in atTop,∀ z∉ rush K x i,
   ‖cup (vote p x) z a b l‖ ≤ C*U.h i^(p.heat+1):=by
     have he(w c):= wanted_p hs x p w c; fin_cases l
     · have ht:=he 0 a; simp only [map_zero,add_zero] at ht;exact ht
     · have ht:=he (step a) b; simp only [wrap_step] at ht;exact ht
     · have ht:=he (step b) a; simp only [wrap_step] at ht;exact ht
     have ht:=he 0 b; simp only [map_zero,add_zero] at ht;exact ht
lemma core_pole (hs:Crown U K)(x:Crew U)(p:Pose)(a b):∃ C≥0,∀ᶠ i in atTop,∀ z∉ rush K x i,
   ‖voice (cup (vote p x) z a b)‖≤ C*U.h i^(p.heat+1+1):=by
    obtain ⟨B,hB,H⟩:=want_step hs x p a b
    obtain ⟨C,hC,L⟩:=want_step hs x p b a; refine ⟨B+C,by positivity,?_⟩
    filter_upwards [H,L] with i hi hh z hz; rw [add_mul]; let V:=vote p x; change ‖V a i z+V b i (z+step a)- V a i (z+step b)-V b i z‖ ≤ _; rw [show V a i z+V b i (z+step a)- V a i (z+step b)-V b i z=(V a i z-V a i (z+step b))-(V b i z -V b i (z+step a)) from by abel]; grw [norm_sub_le]; exact add_le_add (hi _ hz) (hh _ hz)
variable {B:Finset (Crew U)}{x y z:Crew U}{p q t:Pose}
abbrev RimC (B:Finset (Crew U))(K:ℕ→ℕ)(i:ℕ) := Finset.univ (α:=Site (U.M i)) \ B.biUnion (fun x=>rush K x i)
lemma remote (hs:Crown U K)(hx:x∈B)(hy:y∈B)(hz:z∈B)(a b:Axis)(hm:m+4=p.heat+1+1+(q.heat+1)+(t.heat+1)):
   Fruit U m (fun i=>∑ u∈RimC B K i, mx (vote p x) (vote q y) (vote t z) J a b i u) 0:=by
     let X:=vote p x; let Y:=vote q y; let Z:=vote t z
     obtain ⟨C,hC,H⟩:=core_pole hs x p a b; choose R hR V using mx_pole hs y q a b; choose D hD L using mx_pole hs z t a b
     let T:= ∑ p:Fin 4×Fin 4, ‖chi J p‖*R p.1* D p.2; have hp:0 ≤ T:=Finset.sum_nonneg (fun i _=>mul_nonneg (mul_nonneg (norm_nonneg _) (hR _)) (hD _)); apply Fruit.call; apply booze_sake; refine coseal ?_ (mul_nonneg hC hp); filter_upwards [H,eventually_all.2 V,eventually_all.2 L] with i hi hv h; let v:=U.h i; let f(u:Site (U.M i)):= mx X Y Z J a b i u; have he:0 < v:= U.h_pos i
     have hh(u)(hu:u ∈ RimC B K i): ‖f u‖ ≤ (C*T)*v^(m+4):=by
         have h1(b:Crew U)(hp:b∈B):u∉rush K b i:= fun he=> (Finset.mem_sdiff.mp hu).2 (Finset.mem_biUnion.mpr ⟨b,hp,he⟩)
         unfold f mx; rw [norm_mul]; have hy': ‖J (cup Y u a b) (cup Z u a b)‖ ≤ T*v^((q.heat+1)+(t.heat+1)):=by
              rw [chil J]; unfold T; rw [Finset.sum_mul]; apply le_trans (norm_sum_le ..); apply Finset.sum_le_sum; intro l _; rw [norm_mul,norm_mul]; refine (mul_le_mul (mul_le_mul_of_nonneg_left (hv l.1 u (h1 y hy)) (norm_nonneg _)) (h l.2 u (h1 z hz)) (norm_nonneg _) (by have hx:=hR l.1; unfold v at he; positivity)).trans (le_of_eq ?_); unfold v; rw [pow_add (U.h _) (q.heat+1:ℕ) (t.heat+1:ℕ)];ring
         refine (mul_le_mul (hi u (h1 x hx)) hy' (norm_nonneg _) (by unfold v at he; positivity)).trans (le_of_eq ?_); unfold v;rw [hm];ring
     let A:=RimC B K i; grw [norm_sum_le]; apply le_trans (Finset.sum_le_sum (g:=fun _=> (C*T)*v^(m+4)) hh); rw [Finset.sum_const,nsmul_eq_mul]; have hA:(A.card:ℝ)≤U.nb i^4:= by unfold Gloam.nb sizeR; exact_mod_cast ((Finset.card_le_card (Finset.subset_univ A)).trans_eq ((Finset.card_univ.trans (site_card (U.M i))))) -- unfold
     apply le_trans (mul_le_mul_of_nonneg_right hA (by positivity)); apply le_of_eq; change _= _*v^m; rw [pow_add]; change U.nb i^4*(C*T*(_*((U.nb i)⁻¹) ^4))=_; have hx:0<U.nb i:=Pert.Full.val_pos _; field_simp
end YM.OPE.Nestle
