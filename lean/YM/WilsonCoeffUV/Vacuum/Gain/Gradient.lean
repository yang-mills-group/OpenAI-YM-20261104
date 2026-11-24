import YM.WilsonCoeffUV.Vacuum.Gain.DiagonalRows
/-! Keeping track of the fine-address real gradient representative. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Next.Free
open scoped ContDiff Topology BigOperators
variable {G:Gauge} {L n f:Side} {α β : Type*}

abbrev Vix (G:Gauge):= PAC G 0

def well (u:Cover)(j:G.ColorIndex): Cloth (Vix G) := (u, Exterior.vac, j)
def waive (x:Cover)(v:Axis)(i:G.ColorIndex): YForest G:= stone (x,v) i
abbrev ReaderT (L:Side)(G:Gauge):= ropes Cover (Co L (Vix G)) (Hooks G)

-- same column.
def verdant (A F: ropes Cover (Larvae G L) (Hooks G))(Z:ReaderT L G): Prop:= ∀ x v i j,
    spring L F (waive x v i) j-spring L A (waive x v i) j = spring L Z (well (x+step v) i) j - spring L Z (well x i) j

section
variable [Fintype α] [Fintype β]
omit [Fintype α] in
lemma growTS {L:Side} {M:Row (Co L α) β}{s A:ℝ}(h:M.strip s A)(p:0<s)(e:0≤A)(x:Cloth α)(y:Cloth β) : Tendsto (fun n:Side=> installed (ratioN L n) M (foldUnder (n*L) x) (foldUnder n y)) atTop (𝓝 (spring L (shuttleM M) x y)) := by
  have hx:= (matrix_visit h p e).point ((panel L α).symm x) y
  refine hx.congr fun n=>?_
  have he : splitCo (ratioN L n) α (foldUnder (n*L) x)=foldUnder n ((panel L α).symm x):= by
    have he:=panel_wrap (ratioN L n) ((panel L α).symm x); rw [Equiv.apply_symm_apply] at he; rw [he,Equiv.apply_symm_apply];
  unfold installed; dsimp only; rw [Matrix.submatrix_apply,he]; rfl
end

lemma rise_e (n f : Side)(p: Matrix (Body 0 f) (Body 1 n) ℝ)(x : Site f)(v:Axis)(i:G.ColorIndex)(j:Slot G n 1): tensor G (d 0 f*p) (x,coord v,i) j = tensor G p (x+step v,Exterior.vac,i) j- tensor G p (x,Exterior.vac,i) j:= by
  let a: Body 0 f→ℝ:= fun u=> p u (j.1,j.2.1)
  have h : (d 0 f*p) (x,coord v) (j.1,j.2.1)= a (x+step v,Exterior.vac)-a (x,Exterior.vac):=d_sites x v a
  unfold tensor; simp only [Matrix.of_apply,h]; split <;> simp [a]
lemma pocket {α β:Type*}{c f:Side}(g:Ratio c f)(M:Cross g.count α β)(A:Matrix (Co f α) (Co c β) ℝ)(h: M.acts c=A.submatrix (splitCo g α).symm (Equiv.refl (Co c β))) : installed g M=A:=by
   ext1 i j; unfold installed; rw [h]; simp
lemma fiber_leaf (S:StepData n f)(A: PoleRows S.patch)(p : CoarseMean G S.patch)(T: Row (Co S.patch.L (Vix G)) (Hooks G)) {s C:ℝ}(hs:0≤s)(h: (gaugedA G S.patch A).strip s C)
  (hf:T=angle G S.patch (gaugedA G S.patch A))(hp:p.acts n=Stationary.repackM (Stationary.unitSplit G S 1) (Equiv.refl _) (tensor G (extracted S (repeatF S) (installed S.ratio A)))) (i:G.ColorIndex)(x: Site f)(v:Axis)(j:Slot G n 1):
    installed S.ratio p (x,coord v,i) j-installed S.ratio (gaugedA G S.patch A) (x,coord v,i) j = installed S.ratio T (x+step v,Exterior.vac,i) j- installed S.ratio T (x,Exterior.vac,i) j := by
   let Q:=installed S.ratio A; let R:= straighten S (repeatF S) Q
   have hx: installed S.ratio p=tensor G (extracted S (repeatF S) Q):= pocket _ _ _ hp
   have he: installed S.ratio (gaugedA G S.patch A)=tensor G Q:= pocket _ _ _ (cross_backed A Q rfl)
   have hh: installed S.ratio T=tensor G R:=by subst T; exact pocket _ _ _ (angle_period S h hs)
   rw [hx,he,hh,extracted,tensor_add,Matrix.add_apply,add_sub_cancel_left]; exact rise_e ..

variable (A:Levels G) (N m : ℕ)
abbrev groove (A:Levels G)(N m:ℕ):= gaugedA G (loose A m) (predictionA A N m)
abbrev wagon (A:Levels G)(N m:ℕ):= angle G (loose A m) (groove A N m)
lemma pass_width (p:m<N): verdant (shuttleM (groove A N m)) (shuttleM (feedA A N m)) (shuttleM (wagon A N m)) := by
   intro x v i j
   set P:= loose A m
   set L:=P.L
   let M:= groove A N m; let Q:=feedA A N m; let T:= wagon A N m
   obtain ⟨s,hs,H⟩ := schedule_flat A.clock.kernel G _ _ (A.clock.adm (m+1)) (A.clock.adm m); obtain ⟨b,hb,H⟩:= H (loose A m) rfl (A.blocks m 0).branches
   obtain ⟨_,hu,hh⟩ := (H A m rfl rfl rfl).actual N p
   obtain ⟨t,c,ht,hc,hB⟩:= advance_actual (G:=G) A.clock.kernel.penalty A.clock.kernel.penalty_pos (A.clock.adm (m+1)) (A.clock.adm m)
   have h : M.strip t c := by
     have H' := hB A m N rfl rfl rfl [] (Nat.zero_le _)
     refine coloration_paid (G:=G) _ _ _ hc.le (strip_mono (show (predictionA A N m).strip t (c/((loose A m).L.val:ℝ)) from by simpa only [advanceC,List.length_nil,add_zero,pow_one] using H') le_rfl ?_)
     exact div_le_self hc.le (by exact_mod_cast (loose A m).L.property)
   have hp: Q.strip s b:=hu; have hz:T.strip s b:= hh
   -- terms will have ghosts shape
   let u := waive x v i
   let y := well x i; let z:=well (x+step v) i
   have hf := (growTS hp hs hb.le u j).sub (growTS h ht hc.le u j); have h':= (growTS hz hs hb.le z j).sub (growTS hz hs hb.le y j)
   refine tendsto_nhds_unique hf (h'.congr fun n=>?_)
   let S:= mStep A n m; let t' := wagon A N m
   have he: (foldUnder (n*P.L) z)= (wrap (n*P.L) x+step v,Exterior.vac,i):= by simp only [z, foldUnder,well, map_add, wrap_step]
   change installed (ratioN P.L n) T (foldUnder (n*P.L) z) _- _= _; rw [he]; exact (fiber_leaf S (predictionA A N m) Q T ht.le h rfl (feed_period A N m p n (n*P.L) rfl) i (wrap _ x) v (foldUnder n j)).symm
end YM.WilsonCoeffUV.Bank
