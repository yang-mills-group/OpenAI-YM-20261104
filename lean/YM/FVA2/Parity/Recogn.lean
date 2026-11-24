import YM.FVA2.Parity.Lum
import YM.FVA2.Parity.Tailed
/-!
# Reflected worker actually tends to the SAME specified archive
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Parity.Screen
open Function Set Filter Finset Lattice MeasureTheory
open MS MS.Koszul MS.Plane MS.Book MS.Native MS.Native.Orient MS.Native.Chart
open MS.Native.Sew MS.Cylinder MS.Cylinder.Lab MS.Landau MS.Landau.Detect MS.Color MS.Native.Paint
open MS.Momentum MS.Menus MS.Native.Wilsonian MS.City MS.Wind MS.Arts MS.Outlook MS.Tone MS.Logarithm
open MS.Book.Program MS.Book.Convolve MS.Tone.Frame Hue.Agent Hue.Agent.Kappa Position
open MS.Heat MS.Heat.Signal MS.High MS.High.Knobs MS.Land MS.Plane.Wire
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace Classical
variable {J:Type}{m n d i k t:ℕ}{G:Gauge}{p:Team}{r v:ℤ}
local notation "γ"=> grey G Cover
local notation "Ψ"=> Hue.flip (Lane4 G)
abbrev outer (G:Gauge)(n:ℕ) : Law G→ₗ[ℂ] Law G:= Hue.σ n • Hue.flip (Lane4 G)
local notation "φ"=> outer G
lemma weight (F:Dot G Cover): Tone.run (γ F)= Ψ (Tone.run F):= by
    funext l; let g:ℤ:=l.length
    have ht : (l.length:ℤ)=g:= rfl; have he (X:Dot G Cover): run X l=run (model g X) l:= by rw [Tone.grade, enough l ht]
    nth_rw 1 [he]; rw [ Hue.flip_at,he F ]; rw [ grey, ← mod_tag, show graffiti (fun _=> (-1:ℂ)) (model g F)= Hue.σ l.length • model g F from perfect _ ?_, map_smul ]; rfl; intro m hm; exact strange _ (by unfold g; omega)
lemma o (j:ℕ)(F:Law G)(l:List (Lane4 G)): φ j F l= Hue.σ (j+l.length)*F l:= by rw [ Hue.sp,mul_assoc ]; rfl
lemma score_P (i:ℕ)(f: ℝ) (F:Wind.Flow G)(h: TouchF F): φ i (Wiref G F f)= Wiref G ((φ i) ∘ F) f:= by
    have he: TouchF ((φ i) ∘ F):= by
        intro E _ _ u w hu hf; simp_rw [ Function.comp_apply, o, show ∀ z:E,( walk0 w z ).length=w.length from fun z=>List.length_map _ ]; exact ContDiff.mul contDiff_const (h E u w hu hf)
    change φ i ( orbit (Cpu G f) μzone (F f))= orbit (Cpu G f) μzone (((φ i) ∘ F) f); rw [ finite_cc μzone (period0 μzone cour0 (main_f _) h), finite_cc μzone (period0 μzone cour0 (main_f _) he) ]; funext l; rw [o]; simp only [ Ccy, ← integral_const_mul ]; refine integral_congr_ae (Eventually.of_forall (fun x=>?_)); simp only [comp_apply, Flux.at_trc, o, List.length_cons, ← add_assoc, Finset.mul_sum]; simp_rw [Hue.ss,neg_neg]; refine Finset.sum_congr rfl fun i1 _=> Finset.sum_congr rfl fun j _=> mul_left_comm ..
lemma pair (k m:ℕ)(t:ℝ) (F H:Law G): φ (k+m) (boulevard parity (Cpu G t) F H)=boulevard parity (Cpu G t) (φ k F) (φ m H):= by
    simp only [outer, LinearMap.smul_apply,map_smul,smul_smul,Hue.sp]; rw [mul_comm]; congr 1; simp_rw [blvd]; simp_rw [ ← Hue.black (p:=parity) ]; exact Arts.Pilot.Transport.gatherR (Hue.port _) F H ( X_even G t ) ( X_even G t )
-- compare with any actual PM. For multi-laws only in D tower later. need Rank & determinant.
lemma touch (i:ℕ)(F: Flow G)(h:TouchF F): TouchF ((φ i) ∘ F):= by
    intro E _ _ f w hw hf; simp_rw [ Function.comp_apply, o, show ∀ z:E,( walk0 w z ).length=w.length from fun z=>List.length_map _ ]; exact ContDiff.mul contDiff_const (h E f w hw hf)
variable {F H P P': Wind.Flow G}
lemma solely (m:ℕ){A B:Law G}(hm:Rank F v)(hz:Rank H r)(ht: TouchF F)(hs: TouchF H)(hf:Sat A F P)(h: Sat B H P')(hF:B=φ m A)(hp:∀ t, P' t=φ m ( P t )): H=(φ m) ∘ F:= by
    let V:= (φ m) ∘ F; refine sub_eq_zero.mp ( Dtotal (F:= H - V) ⟨ ?_,⟨ max r v,?_⟩,?_ ⟩ ?_ )
    · rw [sub_eq_add_neg]; have hc:= (TouchF.scale (-1:ℂ) ( touch m F ht )); simp only [neg_one_smul] at hc; exact hs.add hc -- fix
    · intro t w hv; simp only [Pi.sub_apply, V, comp_apply,o,hm t w (by omega),hz t w (by omega),mul_zero,sub_self]
    · intro t w' hb; have hh:= ( ( h.2 t w' ).sub (( hf.2 t w').const_mul (Hue.σ ( m+w'.length) ))); simp only [V,comp_apply,map_sub,Pi.sub_apply,o, ← score_P m t F ht]; simp only [Pi.add_apply,hp,o,mul_add] at hh; convert! hh using 1; abel
    simp only [V,Pi.sub_apply, h.1,hF,hf.1,comp_apply, sub_self]
variable {X Q Q': Dec G}{A B: Actor G}
lemma capture (hF:PM A X Q r)(hB:PM B X Q' r)(t i:ℕ)(H:∀ j x, run ( B x j )=φ ( j+t ) (run ( A x j )))(hp:∀ i x s, φ i (X i x s)= X i x s) (x:ℝ): Q' i x=(φ (i+t)) ∘ Q i x:= by
    induction i using Nat.strong_induction_on with
    | h i ih =>
     obtain ⟨m,hm⟩:= ( hB.owes i ).pay; obtain ⟨n,hn⟩:= ( hF.owes i ).pay; refine solely _ ( hn x ) (hm x) ((hF.owes i|>.stay x ).joint) ((hB.owes i |>.stay x).joint) (hF.recu i x) (hB.recu i x) (H i x) ?_; intro v; simp only [path,one_smul,Finset.sum_apply,map_sum]; refine Finset.sum_congr rfl (fun j hj=>?_); obtain he:= (path_in hj).2; rw [ih _ he]; change boulevard parity _ _ _=φ ( i+t) ( boulevard _ _ _ _ ); let S:=X (i-j) x v; nth_rw 1 [ ← show φ (i-j) (X (i-j) x v)=_ from hp _ _ _ ]; exact (( by rw [pair]; rfl ) : ( _ = φ ((i-j)+(j+t)) (boulevard parity (Cpu G v) S (Q j x v)) ) ).trans ( by rw [show (i-j)+(j+t)= i+t from by omega]; rfl ) 
variable (Y:XSpace.Initialize G){U: Booked (Press.portDeck G)}(S:MS_Data G U)
local notation "ℳ"=> Press.wickInput Y
local notation "H"=> Press.portDeck G
open MS.Dock MS.Train MS.LogTime MS.Local.Physical MS.Mach MS.Pearl
lemma paid (T:Acts H d)(h:Correct p)(c:ℝ×ℝ): col (horizonF ℳ p (shaded t T)) i c=φ (i+t) (col (horizonF ℳ p T) i c):= by
    unfold col; rw [capture (aquaF ℳ p T) (aquaF ℳ p _) t i (fun j x=>?_) ]; rfl
    · intro i x s; exact Hue.only_id i _|>.mp ( nav (p:=p) (k:=i) (fun i _=>h.tone i) (skyPC G p) i.le_refl s x ) -- param order
    rw [score_pay Y h,map_smul, Screen.weight ]; rfl
lemma chart_pay {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](x:ℕ)(w:Wire (BH G) E QP)(f:ℝ × ℝ→Law G): Chart (lane meet ((φ x) ∘ f)) w= Chart (Hue.σ (x+w.length) • lane meet f) w:= by
    funext i v; simp only [Chart,Plane.lane,comp_apply,o,Pi.smul_apply,sail_len,smul_eq_mul]
lemma pledged (T:Acts H d)(t:ℕ)(F:Recount G)(hp:∀ i c,Hue.only (i+t) ( F i c )) (h: Correct p)(hF: Fixed (col (horizonF ℳ p T)) F false r 0) : Fixed (col (horizonF ℳ p (shaded t T))) F false r 0:= by
    intro n hn v hv E _ _ w hw ht; let f:= col (horizonF ℳ p T); let P:= (φ (n+t)); have he : F n=P ∘ F n := funext fun x=>(Hue.only_id _ _|>.mp (hp n x)).symm; unfold Light; rw [he, ← show ( (φ (n+t)) ∘ (f n) )=_ from funext (fun x=>(paid Y T h x).symm), chart_pay,show Chart (lane meet (P ∘ F n)) w= _ from chart_pay _ w (F n) ]; exact Light.scalar ( hF n hn v hv E w hw ht ) _
end YM.FVA2.Parity.Screen
