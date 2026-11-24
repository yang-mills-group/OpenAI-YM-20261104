import YM.FVA2.JRad
/-!
# The precisely lifted curvature alphabet. Reach at true filtration.
-/
set_option autoImplicit false
set_option maxHeartbeats 95000
noncomputable section
namespace YM.MS.RadL
open Set Function Filter Finset MeasureTheory Real Maxwell Labels
open Analysis Tensor Koszul Plane Landau Detect Detect.Mark Local.BV InnerProductSpace Submodule Momentum Local
open Theater Mach Lifting Pole Color
open Complex (I)
open scoped Topology Classical ContDiff BigOperators RealInnerProductSpace
variable {G:Gauge}{h k n m:ℕ}{x:E4}
namespace Spray
-- spanning of real evaluation coordinates (all weights)
def familyR (G:Gauge)(k:ℕ): Submodule ℝ ( Module.Dual ℝ (Labels.Taylor G k) ):= Submodule.span ℝ { p | ∃ (y:E4)(i:Axis)(c:G.ColorIndex), p= Spray.α ⟨ k,i,y ⟩ c }
lemma fullR (G:Gauge)(k:ℕ): familyR G k=⊤:= by
    let S:= Labels.Taylor G k; apply Submodule.dualAnnihilator_eq_bot_iff.mp; apply eq_bot_iff.mpr; intro u h;
    obtain ⟨x,rfl⟩:= ( Module.bijective_dual_eval ℝ S ).2 u; rw [Submodule.mem_dualAnnihilator ] at h; have ht : x=0:= by
       apply Labels.Taylor.value_ext; funext i y; ext j; let L:= Spray.α ⟨ k,i,y ⟩ ( G:=G ) j; have H:L∈familyR G k:= by apply subset_span ( R:=ℝ ); exact ⟨ y,i,j,rfl ⟩
       exact h L H
    rw [ht,map_zero]; exact (⊥:Submodule ℝ _).zero_mem
private def gather (G:Gauge) : Local.BV.Grade G→ₗ[ℂ] Law G:={ toFun:= Koszul.mono,map_add':= Koszul.mlin,map_smul':= fun _ _=> Koszul.mcost .. }
def dir (G:Gauge)(k:ℕ): Submodule ℂ (Law G):= Submodule.span ℂ { p|∃ (y:E4)(i:Axis)(c:G.ColorIndex),p= Koszul.mono (Spray.mark ⟨k,i,y⟩ c) }
set_option quotPrecheck false
lemma catches (i:Key G) : Koszul.mono (lamp i) ∈ dir G i.1:= by
    let k:= i.1; let P:= dir G k; let Q(j):= (gather G) (RowLeg G k (Complex.ofRealCLM.toLinearMap ∘ₗ j)); let T:= Labels.Taylor G k;
    let V: Module.Dual ℝ T→ₗ[ℝ] Theater.Witness G k := { toFun j:= Complex.ofRealCLM.toLinearMap.comp j,map_add' x y:= LinearMap.ext fun v=> map_add Complex.ofRealCLM (x v) (y v), map_smul' x z := LinearMap.ext fun v=> map_smul Complex.ofRealCLM x ( z v ) }; let L:= ( (gather G|>.comp ( RowLeg G k ) ).restrictScalars ℝ ).comp V;
    have ht : familyR G k ≤ Submodule.comap L ( P.restrictScalars ℝ ):= by
       apply Submodule.span_le.mpr; rintro f ⟨ y,j,c,rfl⟩; let x:Spray:=⟨ k,j,y⟩; change Koszul.mono ((RowLeg G k) ( x.spot c ))∈P; rw [ show RowLeg G k ( x.spot c )= _ from ( trust x c ).symm ]; exact subset_span (s:={p:Law G|∃(y:E4)(i:Axis)(c:G.ColorIndex),p= Koszul.mono ( Spray.mark ⟨k,i,y⟩ c )}) (show _ from ⟨ _,_,_,rfl⟩);
    rw [fullR] at ht; exact ht (show ( Labels.axes G k|>.coord i.2 )∈(⊤:Submodule ℝ ( Module.Dual ℝ T ) ) from mem_top)
lemma rose (s:Spray)(u:G.El)(i:G.ColorIndex) : advance u ( s.mark i )= ∑ j:G.ColorIndex, wc u j i • s.mark j := by
    unfold mark; rw [ map_sum ]; simp_rw [map_smul, Plaq.weight, Finset.smul_sum ]; rw [Finset.sum_comm ]; simp_rw [smul_comm ( wc _ _ i ) ]; -- includes P.real CLM
lemma polished (s:Spray)(i:G.ColorIndex) : «over» ( s.mark i )= s.mark i:= by unfold mark; simp_rw [ map_sum,map_smulₛₗ,Plaq.cloak ]; simp
end Spray
open Spray
variable (G) in
def roll (m:ℕ) (T:Fin m → Spray)(σ:Lifting.Grid G m): Law G:= Lifting.family m (fun i=> Spray.mark ( T i )) σ
abbrev bill (T:Fin m→Spray):= ∑ k:Fin m,((T k).k+2) -- parser precedence sum..+2?. must parenthesize.
variable (G) in
def cinemaK (h m:ℕ) := span ℂ {p:Law G|∃ (T:Fin m→Spray) (σ:Lifting.Grid G m), bill T=h∧ p= roll G m T σ}
lemma singleS {p u:Law G}(h:p ∈ Spray.dir G k)(hu:u∈ cinemaK G n m): product (Theater.hands G) p u∈cinemaK G (k+2+n) (m+1):= by
    let Z:= product (R:=ℂ) (Theater.hands G); let S:= cinemaK G (k+2+n) (m+1); suffices ht: Spray.dir G k≤ Submodule.comap (Z.flip u) S from ht h
    refine Submodule.span_le.mpr ?_; rintro t ⟨ y,i,c,rfl⟩; let p : Spray:=⟨k,i,y⟩; suffices ht:cinemaK G n m ≤ Submodule.comap (Z (Koszul.mono (p.mark (G:=G) c))) S from ht hu
    refine Submodule.span_le.mpr ?_; rintro v ⟨T,σ,h,rfl⟩;
    let t:= Local.glow ( Lifting.sense G ) m (fun i=> Koszul.mono ( (T i).mark (σ i) )); let Q: Fin (m+1)→ Spray:= Fin.cons p T; let w:Fin (m+1)→ G.ColorIndex:= Fin.cons c σ; have hT :roll G (m+1) Q w= Z (Koszul.mono (p.mark c)) (roll G m T σ):= by unfold roll Lifting.family; rw [ Local.glow_add ]; dsimp only [Q,w,Fin.cons_zero ]; simp only [Fin.cons_succ, Function.comp_def ]; rfl
    change Z _ (roll G _ T σ)∈S; rw [← hT ]; exact subset_span (s:={ f:Law G|∃ (T:Fin (m+1)→Spray) (σ:Lifting.Grid G (m+1)), bill T=k+2+n ∧ f= roll G _ T σ}) (show _ from ⟨ Q,w,(by simp [bill, Q, Fin.sum_univ_succ]; exact congr_arg (k+2+·) h ),rfl⟩ ) -- ζ simp
set_option maxHeartbeats 300000 in
lemma lon (p:Pol G)(hp:Theater.At p (h,n)) : Theater.orbit G p∈cinemaK G h n:= by
    let H(i:ℕ×ℕ)(p:Pol G): Prop:= Theater.orbit G p∈ cinemaK G i.1 i.2;
    change H (h,n) p; refine Theater.axisI H hp ( fun c=>?_ ) ( fun i=>?_ ) ( fun i j f hf hv=>?_ ) ( fun _ i j _ _ hi hj=>?_ );
    · let f:Fin 0→ Spray:=(fun i=>i.elim0); let σ:Lifting.Grid G 0:=fun i=> i.elim0; change Theater.orbit G (MvPolynomial.C c)∈ cinemaK G 0 0; rw [cus,band0,unitθ];
      have hp:roll G 0 f σ∈ cinemaK G 0 0:= by refine subset_span (s:={ f:Law G|∃ (T:Fin 0→Spray) (σ:Lifting.Grid G 0),bill T=0∧ f= roll G _ T σ}) ⟨ f,σ,Fin.sum_univ_zero _,rfl⟩;
      exact Submodule.smul_mem ( cinemaK G 0 0 ) c hp
    · unfold H; rw [map_zero]; exact zero_mem _
    · unfold H; rw [bags,cusp, Prod.snd_add, add_comm _ i.snd ]; exact singleS ( Spray.catches j ) hv -- parser `i.snd dot`
    unfold H; rw [map_add ]; exact add_mem hi hj
variable (G) in
abbrev form (m:ℕ)(T:Fin m→Spray)(σ:Lifting.Grid G m): Law G:= Lifting.breeze ( roll G m T ) σ
def rays (G:Gauge)(h n:ℕ) : Set (Law G):= {p|∃(T:Fin n→ Spray) (σ : Lifting.Grid G n), bill T=h∧ p=form G n T σ}
lemma form_bar (T:Fin m→Spray)(σ:Grid G m): overC (form G m T σ)=form G m T σ:= cloakF _ _ (fun _ _=> Spray.polished ..)
lemma liftgram (W:Law G)(hP:W∈ Local.Physical.Allowed G h n): W∈ span ℝ ( rays G h n ):= by
    obtain ⟨p,hx,rfl⟩:= chooseX hP; let W:=orbit G p; let U:=rays G h n; let Q:=span ℂ U; have ht:Color.Bright W:= hP.2; -- unknown
    have hv: W∈ Q:= by
       rw [ ← mean_identity ( F:=W ) ht.color ]; refine (?_ : cinemaK G h n ≤ Q.comap mean) ( lon _ hx.2 ) ; apply span_le.mpr; rintro u ⟨ T,σ,h,rfl⟩; have h' : mean ( roll G n T σ )=form G _ T σ:= mean_mid _ _ (fun i u k=> rose ( T i ) u k ); change mean _∈Q; rw [h']; exact subset_span ( s:=U ) ⟨ _,_,h,rfl⟩
    change W∈ span ℝ U; have hP: pale W∈ span ℝ U:= Lifting.syntaxP U (fun t hp=> (by obtain ⟨Y,σ,h₀,rfl⟩:= hp; exact form_bar ..)) hv; rw [ pale_identity ht.shadow ] at hP; exact hP
end YM.MS.RadL
