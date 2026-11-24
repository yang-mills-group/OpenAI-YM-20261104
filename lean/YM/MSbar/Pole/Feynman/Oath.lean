import YM.MSbar.Pole.Feynman.Deposit
/-! # Surface controls at positive scale by real momentum polynomials, with logs -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole.PoleVal
open Function Set Filter MeasureTheory Ambient Momentum Age Mellin Symbol Piece Curtain
open scoped Topology ContDiff BigOperators Classical Interval
variable {I : Type} [Fintype I] {F : ℂ→Cloud I} {s:List (Piece I)} {M U V:Finset I} {a:ℤ}
private lemma rescale {k} (h:Vortex k F): Vortex (k+1) (fun z=> z⁻¹ • F z):= by
  obtain ⟨R,H,hr,hp,h⟩:=h; refine ⟨_,H,hr,hp,fun z hz n x=>?_⟩; have hv:z≠0:=hz.2
  change z^_* (z⁻¹*F z n x)=_; rw [pow_succ,mul_assoc, mul_inv_cancel_left₀ hv, h _ hz]
private lemma nowhere {k:ℕ} {H:ℂ→Cloud I} {K:ℕ→Cloud I} (hh:Vortex 0 H) (hp:Vortex 0 ((fun z=> z⁻¹• H z)-purePolar (k+1) K)) : pay H=K 0 := by
  obtain ⟨C,hc,h⟩:=remove (k:=0) (rescale hh)
  simp only [zero_add,pow_one] at h
  let G i:= if i=0 then C else 0
  have he (n:ℕ): purePolar (n+1) G=fun z=>z⁻¹ • C:= by
    induction n with
    | zero => rw [purePolar_up,purePolar_zero]; simp [G]
    | succ n ih=> rw [purePolar_up,ih]; funext z m x; simp [G]
  rw [← he k] at h
  obtain hr:= h.sub hp
  have hv:= pole_unique (C:=K) (D:=G) (k:=k+1) ?_ 0 (by omega)
  · change pay H= _; rw [hv]; change pay H=C; apply paid
    intro n x
    let R:ℂ→Cloud I:=(fun z=> z⁻¹ • H z)-purePolar (k+1) G
    have hx := ends h n x
    have hk := ((tendsto_id (x:=nhds (0:ℂ))|>.mono_left (show approaching ≤ _ from nhdsWithin_le_nhds)).mul hx).add_const (C n x)
    simp only [id_eq,he k,zero_mul,zero_add] at hk; refine hk.congr' ?_
    filter_upwards [(self_mem_nhdsWithin (a:=(0:ℂ)) (s:={0}ᶜ))] with z hz; change z*(z⁻¹*H z n x-z⁻¹*C n x)+C n x=H z n x; have hp:z≠0:=hz; field_simp; ring
  convert hr using 1; abel

lemma strands (h:Stack s M a U V) : ∃ B : ℝ → Cloud I, Ledger M a B ∧ ∀ r:ℝ,0<r → pay (sum s M a r) =B r:= by
  choose k hk using fun i:Fin s.length=>(h.graded (s.get i) (List.get_mem s i)).swirl
  let L:= Finset.univ.sup k
  let J i:= fun z:ℂ=> z⁻¹ • (s.get i).g z
  let P:= ∑ i:Fin s.length, fun r=> roll M ⟨a,(s.get i).l⟩ r (J i)
  obtain ⟨C,hc,hp⟩:= Curtain.arrange Finset.univ (fun i=> (s.get i).l) a M (F:=J) (k:=L+1)
    fun i _=>rescale ((hk i).mono (Finset.le_sup (Finset.mem_univ i)))
  change Soft (P - Curtain.polar (L+1) C) at hp
  refine ⟨C 0,hc 0,fun r hr=>?_⟩
  have he:P r=(fun z=> z⁻¹ • Piece.sum s M a r z):= by
    funext z n x; simp only [P,J,Finset.sum_apply]; rw [unified s M a r]
    simp only [Pi.smul_apply,Finset.sum_apply,smul_eq_mul, Finset.mul_sum]; apply Finset.sum_congr rfl
    intro i _; change _*(z⁻¹*_)=z⁻¹*(_*_); exact mul_left_comm ..
  have hb:= hp.vortex r hr; rw [Pi.sub_apply,he] at hb; exact nowhere (h.combined r hr) hb

lemma unglazed (h:Stack s M a U V): Soft (fun r=>sum s M a r):=by
  choose k hk using fun i:Fin s.length=>(h.graded (s.get i) (List.get_mem s i)).swirl
  let L:= Finset.univ.sup k
  let P:= ∑ i:Fin s.length, fun r=> roll M ⟨a,(s.get i).l⟩ r (s.get i).g
  obtain ⟨C,hc,hp⟩:=Curtain.arrange Finset.univ (fun i=> (s.get i).l) a M (F:=fun i=>(s.get i).g) (k:=L) fun i _=>(hk i).mono (Finset.le_sup (Finset.mem_univ i))
  change Soft (P - Curtain.polar L C) at hp; apply hp.backside; intro r z hr hz
  have he: P r=sum s M a r:=by rw [unified ..]; unfold P; simp only [Finset.sum_apply]
  have ht:= (show Vortex 0 (P r) from he.symm ▸ h.combined r hr).sub (hp.vortex r hr)
  have hg: Vortex 0 (Curtain.polar L C r):= by convert ht using 1; simp
  have hh: Curtain.polar L C r=0:= by
    have hx:= pole_unique (k:=L) (D:=fun _=>0) (C:=fun i=> C i r) ?_
    · unfold Curtain.polar; rw [ext_cut L _ _ hx]; funext; simp [purePolar]
    rw [show purePolar L (I:=I) (fun _=>0)=0 by funext; simp [purePolar], sub_zero]; exact hg
  rw [Pi.sub_apply,he,hh,sub_zero]
end YM.MSbar.Pole.PoleVal
