import YM.FormalBulk08.Broc.Hatch

/-! Export all-order analytic path packets, compared in *each order*,
all exponential width before L. Matches log-link kernels at every position, hence
also Taylor coefficients of their full torus folds for any side. Does
not assert equality in the masks nor p+1 analytic error for the actual. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Broc
open Function Filter Lattice RG Laurent Bloch Exterior Wilson
open Reef Lava Gorge Mesa Shore Lotus Orb Wick Series Jets PowerSeries North Cork City Wine
open Stationary hiding shine Rays
open scoped Topology ENNReal Matrix BigOperators Classical ContDiff
variable {G:Gauge}{n:Side}{r t m e E:ℕ}{A B σ η:ℝ}{T R:Pot G}{P Q:List (LeafD G)}

structure PrintK (T:Pot G)(E e k:ℕ)(σ A:ℝ)(P:List (LeafD G)):Prop extends Edition P E σ A where
    count:P.length≤ k*(E+1)
    scope:∀ p ∈ P,e≤p.u ∧ p.u<e+k
    agrees:∀ i<e+k,binding P i=T i
lemma PrintK.mono (h:PrintK T E e t σ A P)(hs:η≤σ)(hx:A≤B): PrintK T E e t η B P := { h with toEdition:=h.toEdition.mono hs hx }
lemma Sane.sub (h: Sane T E)(ht:Sane R E)(H: Fits T E σ A)(p:Fits R E η B)(hs:0<σ)(hp:0<η): Sane (T-R) E:= fun a i hi hv=> by
    change value a (T i 2-R i 2)=0; rw [value_less ⟨σ,A,hs,H.pay i hi 2⟩ ⟨η,B,hp,p.pay i hi 2⟩ a,h a i hi hv,ht a i hi hv,sub_self]
-- transmission only needs future sanity when starting later.
lemma plus_trim (p:Sheet T e (E+1) P E σ A)(h: binding P e=T e)(hx:Sane T E): Sane (T-binding P) E:= by
    intro a i hi hc; simp only [Pi.sub_apply]; by_cases he: i=e
    · rw [he,h,sub_self]; simp [value,mir,net,hem]
    have he': binding P i 2=0:=by by_contra u;have hh:=no_extra p u;omega
    rw [he',sub_zero,hx a i hi hc]
lemma insideB (p: Sheet T e (E+1) P E σ A)(h:binding P e=T e)(hp: Pale T e): Pale (T-binding P) (e+1) := by
    intro i hi j; by_cases he:i=e
    · simp [he,h]
    push Not at he; rw [Pi.sub_apply,Pi.sub_apply,show binding P i j=0 from ?_, hp i (by omega),sub_zero]
    by_contra z;have he' := (no_extra p z).1;omega
lemma PrintK.fuse (p:Sheet T e (E+1) P E σ A)(q:PrintK (T-binding P) E (e+1) t σ B Q): PrintK T E e (t+1) σ (A+B) (P++Q) := by
    refine {with_edition p.printed q.toEdition with count:=?_,scope:=?_,agrees:=?_} -- replace
    · have ht:=q.count; have he:=p.cap; rw [List.length_append]; rw [add_mul];omega
    · intro a ha; rcases List.mem_append.mp ha with ha|ha; have he:= (p.tags a ha).1;omega
      have he:=q.scope a ha;omega
    intro i hi; rw [binding_two]; simp only [Pi.add_apply,q.agrees i (by omega),Pi.sub_apply, add_sub_cancel]
-- recursion on number of processed grades. preserve residual affine-null
lemma larvae (G:Gauge)(hG:G.Simple)(E k:ℕ)(σ:ℝ)(hs:0<σ):∃ δ K:ℝ, 0<δ ∧ 0≤ K ∧ ∀ i,i+k≤E+1 → ∀ (p:Pot G) A,Fits p E σ A → Temper p E → Sane p E → Pale p i → ∃ P,PrintK p E i k δ (A*K) P:= by
    induction k generalizing σ with
    | zero=> refine ⟨σ,0,hs,le_rfl,fun i _ p A P hp hz hu=>⟨[],?_,?_,?_,?_⟩⟩
             · apply no_edition (by simp)
             · simp
             · simp
             intro e he;simp only [binding_nil]; exact funext fun j=> (hu e (by omega) j).symm
    | succ k ih=>
       obtain ⟨η,K,h,hK,H⟩:= hatch hG hs E; let v:=min η σ;have ht:0<v:=lt_min h hs
       obtain ⟨ξ,C,hC,hx,Q⟩:= ih v ht
       let B:=K+(1+K)*C; have hb:0≤B:= by unfold B;positivity
       refine ⟨min η ξ,B,lt_min h hC,hb,fun i hi p A P hp hz hu=>?_⟩
       have hσ:i≤E:=by omega
       obtain ⟨S,a,b⟩:= H i hσ p hp A P hu (fun c=> hz c i hσ)
       let F:=binding S; have hF:=a.printed.fiscal; have hy: Fits (p-F) E v (A*(1+K)):= by rw [mul_add,mul_one]; exact (P.mono (min_le_right ..) le_rfl).sub (hF.mono (min_le_left ..) le_rfl)
       have hm:= warm_binding a.printed.honest
       obtain ⟨T,hT⟩ := Q (i+1) (by omega) _ _ hy (temper_less hp (float_temp hm E) P hF hs.le h.le) (plus_trim a b hz) (insideB a b hu)
       unfold B; rw [mul_add,←mul_assoc A]; refine ⟨S++T,PrintK.fuse (sheet_mono a (min_le_left ..) le_rfl) (hT.mono (min_le_right ..) le_rfl)⟩
lemma printable (G:Gauge)(hG:G.Simple)(E:ℕ)(σ:ℝ)(hs:0<σ):∃ δ K:ℝ, 0<δ ∧ 0≤ K ∧ ∀ (p:Pot G) A,Fits p E σ A → Temper p E → Sane p E → ∃ P,PrintK p E 0 (E+1) δ (A*K) P:= by
    obtain ⟨δ,K,h,h',H⟩:=larvae G hG E (E+1) σ hs; exact ⟨δ,K,h,h',fun p A H' T S=> H 0 (by omega) p A H' T S (by intro i h; omega)⟩
lemma PrintK.sees (p: PrintK T E 0 (E+1) σ A P)(n:Side): Through E (stone T n) ((P.map (fun a=> mountain (issue a.field) n a.u)).sum):= by
   intro j hj;rw [←book_mountain p.honest]; simp_rw [sow_coeff,sow,p.agrees j (by omega)]
-- consumers before scheduling movement. Instantiate at normalized frames
lemma Sane.frame {X}(h:FrameV T X)(E): Sane T E:= fun a e _ he=> (h.seals e he).water 1 1 a a 0 0
lemma Temper.frame {X}(h:FrameV T X)(E): Temper T E:= float_temp { h with } E
end YM.FormalBulk08.Broc
