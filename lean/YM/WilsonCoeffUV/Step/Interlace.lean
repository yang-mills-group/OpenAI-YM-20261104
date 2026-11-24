import YM.WilsonCoeffUV.Step.Parity
import YM.WilsonCoeffUV.Step.Source
/-! Torus output sampler invariants for unbounded *finite* order testing,
including scalar removal and recalibration. At this point no growth hypotheses!
Reset input readout actually supplied on bulk jets later. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Power
open Lattice Laurent Bloch Exterior Wilson Precision RG Function Filter Metric
open Blue FreeResolvent Tree Matrix PowerSeries Next.Free
open scoped ContDiff Topology BigOperators
variable {c f : Side}{G:Gauge}
lemma rollMix {p p':PChart G c}{s b}(h:rollTest (flash p) (flash p') s b){i j}(hp:shellK i p)(hp':shellK j p'){A:PowerSeries ℝ}(he:constantCoeff A=1) : rollTest (flash (mix A p)) (flash (mix A p')) s b := by
  intro Z H q X X' t
  have hy:= h t
  rw [←redo_stern A hp,←redo_stern A hp']; exact ((DFunLike.congr_fun (redo_com A he X t.f₀) (flash p)).symm.trans ((congrArg (redo A) hy).trans (DFunLike.congr_fun (redo_com A he X' t.f₁) _)))
lemma W_lop {p:PChart G c}{k}(h:Warded (flash p))(u:shellK k p): Warded (flash (lop p)) := by
  intro s b Z H q X X' t
  have he: train (spool X) (flash p)=train (spool X') (flash p) := h s b t
  let w:= PowerSeries.mk (fun i=> p i 0 (fun j=> j.elim0));
  have ht : p = lop p + uband w:= lop_pres p
  have hv : flash p = flash (lop p)+soil w := by conv_lhs=> rw [ht];
                                                 rw [flash_add (finite_shell (shell_lop u)) (finite_shell (uband_length _ _ 2)),uband_flash]
  rw [hv,map_add,map_add,income,income] at he; exact add_right_cancel he

structure Interlace (H:FaceRow)(P:PChart G f) : Prop where
  valid : Warded (flash P)
  shape (k : ℕ): Pure (P k)
  lamp : shellK 2 P
  evenP : PairP P
  stem: P 0=Blue.shine (orbQ (precisionC G f H))
  clear : lop P=P
section
-- Wilson top and startup equality on all tori
lemma W_shape {H:FaceRow}(h:H.acts f=1): Interlace H (lop (sprig (eWilson (G:=G) (c:=f)) 2)) := by
  let W:= eWilson (G:=G) (c:=f)
  let P:=sprig W 2; have he:=sprig_count W 2
  refine ⟨W_lop (top_turn h) he,fun i j=>?_, shell_lop he,?_,?_,?_⟩
  · unfold lop; split; exact Blue.Smooth.zero; exact sprig_pure W W_green 2 _ _
  · intro i j hi; unfold lop; split; rfl; exact shine_dark (by omega)
  · have H:= sprouts_lead (show Green W from W_green) (w_jets (G:=G) h).2.2 (kinetic_sym (by rw [h]; simp))
    change lop P 0 = _; ext1 i; rw [lop,show P 0=_ from (show P 0=_ from H)]
    split; next hi=> rw [shine_dark (by omega)]
    rfl
  ext i r x; unfold lop; split <;> rfl
end

variable (S:StepData c f)(F:Forest S.ratio)(H Y:FaceRow) (Q:Matrix (Body 1 f) (Body 1 c) ℝ)
variable {P:PChart G f}{Ñ:ChartRatio G}

private lemma scrub_pair {U:Type}(P:Pal ℝ U)(p:PairP P) : PairP (scrub P):= by
  intro i j h; rw [scrub]; split; · rfl
  exact p i j h
private lemma fade_pair {U V:Type}[Fintype U] {P:Pal ℝ U}(p:PairP P)(M:Matrix U V ℝ): PairP (fun i=> fade M (P i)):= fun i j h=>funext fun k=> by change fade _ _ _ _= _; rw [fade,p _ _ h]; simp
lemma pair_winter (w:PairP P): PairP (lop (winter S F H Y Q Ñ P)) := by
  let M:= extractV G S F Q; let u:= casePW S Ñ M P
  have ht : PairP u:= pare_sub (pare_sub (fade_pair (P:=sprig (unhaar Ñ) 0) (fun i j h=> shine_dark (by omega)) (camber G M)) (fade_pair (scrub_pair (sprig (jointPen G S) 2) (fun i j h=> shine_dark (by omega))) _)) (fade_pair (scrub_pair P w) _)
  have he (b:ℕ): PairP (xray S F H Q Ñ P b):= order_parity _ ht b
  have hp : PairP (summer S F H Q Ñ P) := by
    unfold summer; apply fade_pair; intro i j h; simp_rw [Finset.sum_apply]; exact Finset.sum_eq_zero fun a _=>he a i j h
  intro i j h; rw [lop]; split
  · rfl
  rename_i hz
  have hx: flatPal (precisionC G c Y) i j = 0:= by
    unfold flatPal; split; next hu => exact shine_dark (by omega)
    rfl
  simp_rw [winter,Pi.add_apply,Pi.sub_apply,hx,hp _ _ h]; rw [uband,shine_dark (by omega)]; simp
lemma drawTop (A:Levels G) (n:Side)(N:ℕ) : (freeForms A N N).acts n=1 := by
  let j:=A.clock.J N
  let R:= Train.top j
  let k:=A.clock.kernel.penalty
  have hk:=A.clock.kernel.penalty_pos; have hj:=A.clock.adm N
  let X:=record (pulse k R)
  change (freeForms A N N).acts n=1
  unfold freeForms; rw [loc_top]
  have hh := (heart_heats A.clock.kernel.penalty hk hj (id : Train j→Train j)).1
  have he := Whole.eq_on (hh.stock.whole R) (Whole.coin (TypeFace 2)) (fun p hp=> ((heart_true _ hk hj R).1.echo _ hp).trans ((top_metric _ hk j (base_subset_realCube zone_pos hp)).2.trans (read_unit _ p).symm)) n
  rw [Work.F08.acts_unit] at he; exact he

lemma reclosed (hS:S.patch.Branches S.kernel G)(h:LocalRatio Ñ) (v:Interlace H P)
    (a: IsUnit (treeMatrix G S F H).det)(k:Inputs S Q (H.acts f) (Y.acts c))
    (p:(H.acts f).transpose=H.acts f)(p':(Y.acts c).transpose=Y.acts c)
    (A:PowerSeries ℝ)(hc:constantCoeff A=1)(he:evenC A): Interlace Y (mix (back A) (lop (winter S F H Y Q Ñ P))) := by
  let T:=winter S F H Y Q Ñ P; let U:=lop T
  have hx : shellK 2 T := winter_band S F H Y Q h v.lamp
  have hf : Warded (flash T) := survives S F H Y Q v.lamp v.stem hS h a k p v.valid v.shape
  have hv : ∀ i,Pure (T i) := winter_pure S F H Y Q h hS v.shape p'
  have hy : shellK 2 U := shell_lop hx; change Interlace Y (mix (back A) U)
  have hd : ∀ i,Pure (U i):= by intro i j; unfold U lop; split; exact Blue.Smooth.zero; exact hv i j
  refine ⟨fun s b=>rollMix (W_lop hf hx s b) hy hy (back_cc hc), mix_pure hd,mix_length hy,pair_mix (pair_winter S F H Y Q v.evenP) (back_cc hc) (even_back hc he),?_,?_⟩
  · rw [mix_lead (back_cc hc) U]; ext1 i; unfold U lop
    split
    next H=> rw [shine_dark (by omega)]
    rw [show T 0= _ from winter_calm S F H Y Q h]
  ext1 i; ext1 j; rw [lop]; split
  next hh=> subst j; unfold Blue.mix U; simp [lop]
  rfl
end YM.WilsonCoeffUV.Power
