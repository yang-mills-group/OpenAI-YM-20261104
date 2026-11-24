import YM.FVA2.Rank.Ray
/-! # TaylorOK forbids misplaced power terms in Team

The two paths `Tide.remove` and `Dial.LPT_to_MS` each provide a witness. This forces
each such team to have the required coupling and field parity (see in particular
`Rank/Kappa.lean`). No uniqueness
claim on their mark coefficients. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Hue.Agent.Signal
open Function Filter Set Finset Lattice MeasureTheory Real
open MS MS.Plane MS.Momentum MS.Arts MS.Koszul MS.Landau MS.Landau.Detect
open MS.Native MS.Native.Wilsonian MS.Book MS.Book.Program MS.Book.Convolve MS.Dock MS.Train MS.Pearl MS.Emit
open MS.Wind MS.Wind.Modeled MS.Heat MS.Heat.Signal MS.High MS.Tone MS.Tone.Frame MS.Menus MS.City
open MS.Outlook MS.LogTime MS.LogTime.IntervalFamily MS.Plane.Wire MS.Plane.Domain MS.High.Knobs MS.Motif MS.Land
open Complex (I)
open scoped Topology ContDiff BigOperators Classical InnerProductSpace
variable {G:Gauge}{p q:Team}{n k a:ℕ}{v:ℤ}
variable {s:ℝ→Law G} {X:T ( Flats G )} {Y:T (Coat G)} (h:G.Simple) (hM:leader G X (gloss (pulseX G)) Y)
variable (ht: Fixed ( col ( skyline G p ) ) ( Archive 4 X ) true 4 1 )
   (ih:∀ i, i<n → Spare i (p i))
-- actual adjustment directions
private def sheer (p:Team)(n:ℕ): Team:= fun i=> { p i with coupling:= if i=n then 0 else (p i).coupling }
private lemma sheer_birth (p:Team)(h:k<n): p k= sheer p n k:= by simp [sheer,h.ne]
include h
lemma shade (p:Team)(hx:1 < n): Career G p (sheer p n) n 3 4 (fun i=> (((p n).coupling.eval i:ℝ):ℂ) • Menus.LE G 4):= by
   let q:= sheer p n;
   have hv x: style G p x n-style G q x n= ((((p n).coupling.eval x:ℝ):ℂ)) • Native.Wilsonian.core G 1:= by rw [style_diff x (fun i hi=>sheer_birth _ hi) (by omega),ferryPlan x (p:=p) (q:=q) (fun _=>rfl) (fun _=>rfl),sub_self,add_zero]; congr 1; simp [shift,sheer,Nat.ne_of_gt hx, show n≠0 from (by omega)]
   exact ⟨fun i hi=>sheer_birth _ hi,(fun x=> by rw [hv]; exact Limit.smul _ (Native.Wilsonian.participates G 1)),fun x=> by rw [hv]; exact Lifting.Fits.smul _ (bulk_three h)⟩ -- name Lifting
-- select actual nonabelian triple
lemma marked : ∃ i j k:G.ColorIndex,Mark.LieColor i j k≠0:= by
    obtain ⟨x,y,hx⟩:= h.nonabelian; by_contra he; push Not at he; let e:= EuclideanSpace.basisFun G.ColorIndex ℝ; have hu (i j:G.ColorIndex) : G.ad (e i) (e j) = 0:= by
      let v:G.Color:= G.ad (e i) (e j); change v=0; rw [ ← e.sum_repr v ]; apply Finset.sum_eq_zero; intro k _; rw [ OrthonormalBasis.repr_apply_apply, real_inner_comm, show ⟪v,e k⟫_ℝ=0 from he i j k, zero_smul ] -- guess
    apply hx; rw [← e.sum_repr x,← e.sum_repr y]; simp_rw [map_sum, map_smul, LinearMap.sum_apply,LinearMap.smul_apply, hu, smul_zero, Finset.sum_const_zero ]; simp
omit h
in
private lemma s_g (p:Team)(i:ℕ)(h:i%2=0): Spare i (sheer p i i):= ⟨fun hp=> (hp h).elim,fun hp=> (hp h).elim,fun _ _=> by simp [sheer]⟩
include hM ht ih
lemma pure_g (he:n%2=0)(hx:1<n) (y:ℝ): (p n).coupling.eval y=0:= by
    obtain ⟨i,j,k,H⟩:= marked h; let W:List (Lane4 G):= [Detect.S i 0,Detect.C j 0,Detect.C k 0]; have hh: Wage n (sheer p n):= by intro i hi; obtain h|h:= lt_or_eq_of_le hi; rw [← sheer_birth _ h]; exact ih _ h; subst i; exact s_g _ _ he
    have hX:= Signal.cancel (s:=fun y=> (( (p n).coupling.eval y:ℝ ):ℂ) • Menus.LE G 4) (a:=0) y W h hM (by omega) ht (shade h p hx) (by omega) hh (fun _=>by simp [W,C,Detect.S,net,qnote]) rfl rfl (by decide); -- careful rfl decide
    change (↑((p n).coupling.eval y):ℂ) * Mark.token (Menus.LE G 4) i j k=0 at hX; rw [token_R] at hX; exact Complex.ofReal_eq_zero.mp ((mul_eq_zero.mp hX).resolve_right ( Complex.ofReal_ne_zero.mpr H ))
omit h hM ht ih
abbrev snip (p:Team)(i:ℕ): Team:= rush p (- (p i).waveA) (-(p i).waveC) i
lemma s_w (p:Team)(i:ℕ)(h:i%2=1): Spare i (snip p i i):= ⟨fun _=>by simp [snip,rush],fun _=>by simp [snip,rush],fun _ _=>by omega⟩
include h hM ht ih
lemma pure_w (he:n%2=1)(y:ℝ): ( p n ).waveA.eval y=0 ∧ ( p n ).waveC.eval y=0:= by
    obtain hn:1 ≤ n:=(by omega); let q:= snip p n; let u:= -(p n).waveA; let v:= -(p n).waveC; have hx:= scale_car (G:=G) p u v hn; let V'(x:ℝ):=ranktwo (G:=G) (2*u.eval x) (v.eval x-u.eval x)
    have hW (w:List (Lane4 G))(m:ℕ)(hp:net w=0)(hP:fieldDim wfield w+m=(4:ℤ))(hL:w.length=2): V' y w=0:=Signal.cancel y w h hM hn ht hx (by omega) (fun i hi=>by rcases lt_or_eq_of_le hi with h|h; rw [← rushed h]; exact ih _ h; subst i; exact s_w _ _ he) (fun _=>hp) hL hP (by decide)
    obtain ⟨i⟩:= color_ne h; let a:Axis:=0; let b:Axis:=1; have hb:b≠a:= (by decide +kernel); let Q:FourP:=spray a; have ha: Q a=1:= (by simp [Q,spray]); have hba: Q b=0:= (by simp [Q,spray,hb]); have hs : Q.sq=1:=by simp [ Momentum.sq,Q, spray,Pi.single_apply,ite_pow ] -- op
    obtain ha':= hW [Detect.W b i Q,Detect.W b i (-Q)] 2 (by simp [Detect.W,qnote,net]) rfl rfl
    obtain hb':= hW [Detect.C i Q,Detect.U a i (-Q)] 1 (by simp [C,U,qnote,net]) rfl rfl
    simp [V',ranktwo,Detect.W,C,U,qnote,kinds,Landau.precision,delta,hba,hs,u,v,ha] at ha' hb'
    exact ⟨ha',by rw [ha'] at hb'; simpa using hb'⟩
omit ih
-- complete
lemma all (n:ℕ): Spare n (p n):= by
    induction n using Nat.strong_induction_on with
    | _ n ih=>
        rcases (show n%2=0∨n%2=1 from by omega) with hT| hT
        · exact ⟨ fun hk=> False.elim ( hk hT ),fun hk=>False.elim (hk hT),fun hp _=> Polynomial.funext fun x=> (pure_g h hM ht ih hT (by omega) x).trans Polynomial.eval_zero.symm ⟩
        exact ⟨ fun _=>Polynomial.funext fun x=> by simpa using (pure_w h hM ht ih hT x).1,fun _=>Polynomial.funext fun x=>by simpa using (pure_w h hM ht ih hT x).2,fun _ _=>by omega⟩
end YM.FVA2.Hue.Agent.Signal
