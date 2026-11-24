import YM.WilsonCoeffUV.Product.Connected.FirstJoin
/-!
# Profile center and native translations
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Soil
open Gauge Power PathCost Precision Embroider Fountain Cosmos Shard Realm
open PowerSeries
open scoped Topology BigOperators
variable {n:Side}{U V α β ι:Type*}{r h D j m e i i' j' l k u a:ℕ}{A B C s:ℝ}{G:Gauge}
variable {p q:ProfileW}{D' t η K M s S δ:ℝ}
variable {b:ℕ}
open Wilson Tree AnalyticNext.QuarticMatch.Sheets Exterior Planned.PrimaryIntegral295
variable {c f n:Side}
-- `R` commutes translations of coarse lattice on all periods.
abbrev skewV {A:Type*}{P:Type*}[AddGroup A](d:A)(W:Pal P (A×α)):Pal P (A×α):=fun i j=>revolve d (W i j)
lemma skew_shell {V:Type*}[NormedAddCommGroup V](X: Pal V (Co c α))(p:shellK k X)(d:Site c): shellK k (skewV d X):=by intro i j h; unfold skewV revolve; rw [p _ _ h]; rfl
lemma skew_pure (T: Pal V (Co c α))(d:Site c)(p:Pure (T i)): Pure (skewV d T i):=fun r σ x=> p r σ (jog (-d) ∘ x)
lemma pyre {P: Pal ℝ (Woods G c)}(d:Site c)(hp:shellK k P)(x:rollTest (flash P) (flash P) 1 0): rollTest (flash (skewV d P)) (flash P) 1 d:=by
   intro Z I z T T' H; let M:= spear (jog d:Woods G c≃Woods G c); let R: Lawn Z→ TreeVars G c:=fun i=>M*ᵥ T i
   have hv : TurnsG 1 0 z R T':=by
       refine ⟨(ContDiffAt.comp (g:=fun i=>M *ᵥ i) _ (by rw [H.f₀]; exact board _) H.g₀),H.g₁,(show M*ᵥ T 0=0 by rw [H.f₀,mulVec_zero]),H.f₁,H.gauge,H.shift.mono ?_⟩
       intro i h; unfold R M; rw [h,mantle_reads, Lattice.pull_id]
   change train (spool T) (flash (fun j r=>revolve d (P j r)))= _; rw [value_root _ _ _ hp T H.g₀ H.f₀]; exact x hv
lemma linkReed (S:StepData c f)(V:Forest S.ratio)(Ñ: ChartRatio G)(p:LocalRatio Ñ)(H Y:FaceRow)(Q:Matrix (Body 1 f) (Body 1 c) ℝ)(e:S.patch.Branches S.kernel G)(u:IsUnit (treeMatrix G S V H).det)(ha:Inputs S Q (H.acts f) (Y.acts c))(hb:(H.acts f).transpose= H.acts f)(x:PChart G f)(y:Interlace H x) {P:Pal ℝ (Woods G f)}(t:shellK k P)(hv:∀ i,Pure (P i))(g:rollTest (flash P) (flash P) 1 0) (w:Site c):
    reed S V H Q Ñ x k (skewV (S.ratio.embed w) P)= skewV w (reed S V H Q Ñ x k P):=by
    let T:= skewV (S.ratio.embed w) P; let R:= reed S V H Q Ñ x k P; let U:=reed S V H Q Ñ x k T; have hX:shellK k T:= skew_shell P t _; have hQ i:Pure (T i):= skew_pure _ _ (hv i); have hz : rollTest (flash U) (flash R) 1 w:= reed_turn S V H Q Y y.lamp y.stem p k hX t e hb y.shape hQ hv u ha y.valid (pyre _ t g)
    let M:= spear (jog w:Woods G c≃Woods G c); funext i j; change U i j= revolve w (R i j); rw [surname hz (reed_band S V H Q k y.lamp p hX) (reed_band S V H Q k y.lamp p t) (reed_smooth S V H Q k Ñ _ hQ) (reed_smooth S V H Q k Ñ _ hv) M 1 (fun i=>by rw [show mantle (M*ᵥ i)=_ from mantle_reads w i]; ext1 v; simp [Lattice.gauge]),retail₁]

section
variable [NormedAddCommGroup V][NormedSpace ℝ V]
lemma ply_skew (X:Pal V (Co c α))(t:V→ₗ[ℝ]ℝ)(d:Site c) : ply t (skewV d X)= skewV d (ply t X):=rfl
lemma basisHear (v w:V)(h:∀ f:V→ₗ[ℝ]ℝ,f v=f w): v=w:=by
   let B:= Module.Free.chooseBasis ℝ V; apply B.repr.injective; ext1 i; exact h (B.coord i)
lemma linkWood (S:StepData c f)(M:Forest S.ratio)(Ñ:ChartRatio G)(p:LocalRatio Ñ)(H Y:FaceRow)(Q:Matrix (Body 1 f) (Body 1 c) ℝ)(e:S.patch.Branches S.kernel G)(u:IsUnit (treeMatrix G S M H).det)(ha:Inputs S Q (H.acts f) (Y.acts c))(hb:(H.acts f).transpose=H.acts f)(x:PChart G f)(y:Interlace H x){P:Pal V (Woods G f)}(t:shellK k P)(hv:∀ i,Pure (P i))(g:Cert P)(w:Site c): reed S M H Q Ñ x k (skewV (S.ratio.embed w) P)= skewV w (reed S M H Q Ñ x k P):=by
    let R:= reed S M H Q Ñ x k (R:=V); let Y':= skewV (S.ratio.embed w) P; let Z:=skewV w (R P); funext i j l; apply basisHear; intro f'; change ply f' (R Y') i j l=ply f' Z i j l; apply congr_fun (f:=ply f' (R Y') i j); apply congr_fun (f:=ply f' (R Y') i); apply congr_fun (f:=ply f' (R Y')); unfold Z; rw [ply_skew]; rw [show ply f' (R Y')= _ from reed_maps S M H Q k f' (w:=Y'), show ply f' (R P)=_ from reed_maps S M H Q k f' (w:=P)]; exact linkReed S M Ñ p H Y Q e u ha hb x y (ply_shell f' t) (fun i=> ply_pure _ (hv i)) (g f') w
lemma mixed_shift (X:Parcelized V G n) (B:Cost)(w:Site n): Blue.mix B (skewV w X)= skewV w (Blue.mix B X) := by
   funext i j v; unfold Blue.mix skewV revolve; simp only [Pi.smul_apply, Finset.sum_apply]
def shifted (X:Era G V)(o:Cover):Era G V:= ((fun n=> skewV (wrap n o) (X.1 n)),skewV o X.2)
lemma move_cap (d:Bank.Distance U)(o p:U)(x:dock U α r): tread d o x≤ tread d p x+d.gap o p:=by
   let T:= stud o x; let X:=stud p x; let m:= tread d p x; have he (l:Fin r): d.gap o ((x l).1) ≤ m+d.gap o p:= (d.tri o p _).trans ((Nat.add_le_add_left (leg_le d X 0 l.succ) (d.gap o p)).trans_eq (add_comm _ m))
   apply league_le d T; intro i j; refine Fin.cases (Fin.cases ?_ he j) (fun k=> Fin.cases ?_ ?_ j) i
   · change d.gap o o≤_; rw [d.self]; omega
   · rw [d.swap]; exact he k
   exact fun j=> (leg_le d X k.succ j.succ).trans (Nat.le_add_right ..)
omit [NormedSpace ℝ V] in lemma bendShift {P:raw α V i}{T:Ten V (Cloth α) i}{x y:Cover}(v:Bends x P T): Bends y P T:=by
   obtain ⟨s,a,hs,H⟩:=v.price; let m:= Bank.terrain.gap y x
   refine ⟨v.point,s,a*Real.exp (s*m),hs,(H.and (now_gap y x)).mono fun n ⟨h,t⟩=>⟨mul_nonneg h.1 (by positivity),fun u=>?_⟩⟩; rw [mul_assoc,←Real.exp_add]; apply (h.2 u).trans (mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) h.1); have hx:= move_cap (tor n) (wrap n y) (wrap n x) u; rw [t] at hx; let X:= tread (tor n) (wrap n y) u; let Y:=tread (tor n) (wrap n x) u; have he: (X:ℝ)≤ (Y:ℝ)+m:= by exact_mod_cast hx
   change -s*(Y:ℝ)≤ s*(m:ℝ)+ -s*(X:ℝ); linarith only [mul_le_mul_of_nonneg_left he hs.le]
lemma Auth.shifted {X:Era G V}(p:Auth k X)(o:Cover): Auth k (shifted X o):=by
    refine ⟨fun i j=> bendShift ((p.wing i j).turn o),fun i=>skew_shell _ (p.span i) _,fun n i=>skew_pure (X.1 n) _ (p.pale n i),fun n L=>?_⟩
    intro Z I z A A' H; have hu:= rotation_needed 1 _ _ (ply_shell L (p.span n)) (ply_shell L (p.span n)) (p.token n L) (wrap n o) H; rw [Signed.act_one] at hu; exact hu
variable {m N:ℕ}{X:Era G V}
lemma outing [CompleteSpace V](A: Levels G){Ñ:ChartRatio G}(t:m<N)(g:G.Simple)(f:LocalRatio Ñ)(p:Auth k X)(w:Cover): verseI A Ñ m N k (shifted X ((A.S.block m).val • w))= shifted (verseI A Ñ m N k X) w:=by
    apply Auth.ext (Auth.verse A t g f (p.shifted _)) ((Auth.verse A t g f p).shifted _)
    funext n; let P:= ll A m; let K:=A.clock.kernel; let H:= freeForms A N (m+1); let Y:= freeForms A N m; let Q:=roam A N m n; let x:=(story A Ñ N (m+1)).1 (n*P.L); let b:=wrap n w; let S:=stepAt P K n; let O:=xree P K n; let B:=ratioHigh A Ñ N m; let U:= X.1 (n*P.L)
    have hv:= (old A Ñ g f N (m+1) t).basis (n*P.L); change Blue.mix B (reed S O H Q Ñ x k (skewV (wrap (n*P.L) (S.ratio.count.val • w)) U))=skewV b (Blue.mix B (reed S O H Q Ñ x k U)); rw [show wrap _ _= S.ratio.embed b from Eq.symm (S.ratio.embed_wrap _),linkWood S O Ñ f H Y Q (A.blocks m 0).branches ((cond_laws A m N).1 n _ rfl) (horizon_step A m N t n _ rfl) (age_sym ..) x hv (p.span _) (p.pale _) (p.token _),mixed_shift]
end
end YM.WilsonCoeffUV.Mer
