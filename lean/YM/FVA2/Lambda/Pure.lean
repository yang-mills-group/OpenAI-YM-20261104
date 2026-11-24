import YM.FVA2.Lambda.Bounds
/-!
# Top-rank in native PC heat, independent of shift

 For the indicated PC data. For all y, not assuming polynomial
 in log μ; not requiring zero choices for earlier ranks. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Lambda.Finite
open Function Filter Set Finset MeasureTheory Real Metric
open Lattice MS MS.Plane MS.Momentum MS.Koszul MS.Native MS.Landau MS.Tone MS.Tone.Frame MS.Native.Wilsonian MS.Book MS.Book.Convolve MS.Book.Program
open MS.City MS.Heat MS.Heat.Signal MS.Wind MS.Menus MS.Landau.Detect
open MS.Cylinder MS.Cylinder.Lab
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} {n:ℕ} (p:Team)
lemma funds (i:ℕ)(w:List (Lane4 G))(A:Dot G Cover)(x:ℝ): Tone.run (Program.train (Y p x) i A) w= PowerSeries.coeff i ( (w.map (fieldV p x ∘ Prod.fst)).prod ) * Tone.run A w := by
 unfold Tone.run train; let U:= Y (G:=G) p x; let V:= fieldV p x ∘ (Prod.fst:Lane4 G→ Branch G Axis); apply Eq.symm; exact congr_fun ( pennantC _ A U V paywave (fun i j h=> Eq.symm (congr_arg (fieldV p x) (in_light i j h))) ) w
lemma pristine (x:ℝ)(w:List (Lane4 G))(h:w.length=n+2) : Tone.run (style G p x n) w=Tone.run (core G n) w:= by
 unfold style wobble; rw [LinearMap.comp_apply, rolls,map_sum,Finset.sum_apply, Finset.sum_eq_single (0,n), frame_clock ]; -- rewrite occurrence
 · rw [rules, map_sum, Finset.sum_apply,Finset.sum_eq_single n ]; · rw [ show Program.cut ( Program.shift p x ) n n=1 from (Reg.Token.stamp_n _ ( share .. ) n).trans (by rw [ann, one_pow]),one_smul ]
   · intro b hb hi; rw [map_smul, Pi.smul_apply, Tone.oneRank ( participates G b ) w ( by have hm:= mem_Iic.mp hb; omega ),smul_zero]
   simp
 · intro b hb he; obtain hm:=mem_antidiagonal.mp hb; have hh:b.2<n:= by contrapose! he; exact Prod.ext (by dsimp only; omega) (by dsimp; omega)
   change Tone.run (train (Y p x) _ _) _=_; rw [ funds ]; -- -- maybe no
   rw [ show Tone.run _ w=0 from ?_, mul_zero ]; -- limit
   rw [ rules,map_sum, Finset.sum_apply ]; refine Finset.sum_eq_zero fun i hi=>?_ ; obtain he':= mem_Iic.mp hi; rw [map_smul,Pi.smul_apply, Tone.oneRank (participates G i) w (by omega),smul_zero]
 simp
variable {X:Dec G}{p:Team}(he:PC G p X)
include he
local notation "H"=> ( (1/2:ℝ) )
lemma top_loop (y:ℝ)(n:ℕ)(s:ℝ)(w:List (Lane4 G))(hw:w.length=n+2) : Wiref G (X n y) s w=0:= (lapid_max ( ( he.owes n ).stay y|>.joint ) ( main_f _ ) ( ranked he n y )) s w (by omega)
lemma highest (x y t:ℝ)(w:List (Lane4 G))(hw:w.length=n+2): X n x t w=X n y t w:= by
 induction n using Nat.strong_induction_on generalizing t w with
 | _ n ih=>
     by_cases hp:n=0; · subst n; rw [ he.free ]; rfl
     obtain ha:= he.recu n ( Nat.pos_of_ne_zero hp ) x; obtain hb:= he.recu n ( Nat.pos_of_ne_zero hp ) y
     have hl i (hi:i∈ Domain.paths n 1)(t:ℝ): treeP G ( X (n-i) x ) ( X i x ) t w= treeP G ( X (n-i) y ) ( X i y ) t w:= by
         change Flux.tree _ _ _ _ _= Flux.tree _ _ _ _ _ ; apply scatter_congr; intro l r hr; unfold Flux.attaches; dsimp only; refine Finset.sum_congr rfl fun a _=> Finset.sum_congr rfl (fun b _=>?_ )
         obtain hu:= split_length hr; obtain hV:= path_in hi; have hq:n-i<n:= by omega
         -- exact ranks forced
         simp only [LinearMap.proj_apply]
         rcases lt_trichotomy (n-i+1) l.length with h|h|h
         · rw [ranked he (n-i) x t ((a,-net l)::l) (by simp; omega),ranked he (n-i) x t ((b,-net l)::l) (by simp; omega), ranked he (n-i) y t ((a,-net l)::l) (by simp; omega), ranked he (n-i) y t ((b,-net l)::l) (by simp; omega)]; ring
         · rw [ih _ hq t ((a,-net l)::l) (by simp; omega), ih _ hq t ((b,-net l)::l) (by simp; omega), ih _ hV.2 t ((b,- -net l)::r) (by simp; omega), ih _ hV.2 t ((a,- -net l)::r) (by simp; omega)]
         rw [ranked he i x t ((b,- -net l)::r) (by simp; omega), ranked he i x t ((a,- -net l)::r) (by simp; omega),ranked he i y t ((b,- -net l)::r) (by simp; omega),ranked he i y t ((a,- -net l)::r) (by simp; omega)]; ring
     have hd(s:ℝ): HasDerivAt (fun t:ℝ=> X n x t w-X n y t w) 0 s:= by
         convert! (ha.2 s w).sub (hb.2 s w) using 1; rw [ Pi.add_apply, Pi.add_apply, top_loop he x _ s w hw,top_loop he y _ s w hw ]; refine Eq.symm (sub_eq_zero.mpr ?_); unfold Wind.path; simp only [Pi.smul_apply, Finset.sum_apply]; rw [Finset.sum_congr rfl (fun i hi=> hl i hi s)]
     apply sub_eq_zero.mp; rw [Wind.constancy hd, ha.1,hb.1, pristine p x w hw, pristine p y w hw,sub_self]
end YM.FVA2.Lambda.Finite
