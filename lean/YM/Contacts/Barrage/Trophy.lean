import YM.Contacts.Barrage.Stakes
namespace YM.Contacts.Barrage
open Function Set Finset Filter RG Wilson Lattice Precision Exterior Push.AbsoluteSums Extra.Iteration
open Bloch Milling Milling.Steam Pulse Spine MergeProof Milling.Forge Laurent Stationary Matrix Work.F08
open Milling.Garf Form House PertExtension.Series Tree Larch FreeResolvent PhysicalNext.RankCovariance
open scoped Topology BigOperators Matrix Classical NNReal ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}
namespace Reserve
open Origin Slope Ion Resetter Lumen Next.Free Extension.UV.Linear
namespace Oasis
open Balance
variable {ι X:Type} [Fintype ι] {D: Gauge} {p:ℕ→Pulse.Range X}{F:ℕ→ℕ→ Field ι X} {H:ℕ→ℕ→Prop}
variable {T:Pulse.Range X}{M:ℕ→Field ι X}{Y:Field ι X}{b:ℝ}
lemma accrued (hv:∀ᶠ i in atTop, Rooted T (M i) b) (h:∀ x,Tendsto (fun i=> M i x) atTop (𝓝 (Y x))) : Rooted T Y b := by
   let A:=hv.exists; obtain ⟨i,hi⟩:= A; refine ⟨hi.cash,fun j x=>?_⟩; apply budget_of_sum (fun _=> mul_nonneg (norm_nonneg _) (NNReal.coe_nonneg _)); intro p; refine le_of_tendsto (tendsto_finsetSum p (fun i _=> (h i.val).norm.mul_const _)) (hv.mono fun i hi=>?_ )
   let H:= hi.row j x; exact (H.2.1.sum_le_tsum p (fun j _=> H.1 j)).trans H.2.2
variable {e:Oasis G}
theorem drops_low (i:ℕ): Tendsto (e.η i) atTop (𝓝 0):= by unfold η; exact Real.tendsto_exp_atBot.comp (((tendsto_neg_atTop_atBot.comp (Filter.tendsto_atTop_add_const_right _ _ e.a.S.divergent)).atBot_div_const (by norm_num : (0:ℝ)<4)).congr (by intro j; simp only [Function.comp_apply]; rw [sub_eq_add_neg])) -- congr orientation
lemma point [Nonempty ι](h: Balance.Shade e H p F) (hh:∀ i,∀ᶠ N in atTop,H i N) (i:ℕ) (x:ι→X) : ∃ y:ℝ, Tendsto (fun j=> F i j x) atTop (𝓝 y):= by
   inhabit ι; obtain ⟨t,ht,hg⟩:= h; refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff.mpr fun ε he=> ?_); have hp:= (drops_low (e:=e) i).const_mul (t i); obtain ⟨N,hN⟩:=eventually_atTop.mp (((hp.eventually_lt_const (by simpa only [mul_zero])).and (hh i))); refine ⟨N,fun m hm n hn=>?_ ⟩; have hl:= (hN (min m n) (le_min hm hn)).1; rw [dist_eq_norm]; exact ((hg i m n (hN _ hm).2 (hN _ hn).2).bound x default).trans_lt hl
-- coherent *cover* starbulk limits, no IR choice
structure Stone (e:Oasis G)(p:ℕ→Pulse.Range X)(H:ℕ→ℕ→Prop)(F:ℕ→ℕ→Field ι X)(L: ℕ→ Field ι X): Prop where
   shine i x:Tendsto (fun j=> F i j x) atTop (𝓝 (L i x))
   comes : e.Permit (fun i b=> Rooted (p i) (L i) b ∧ ∀ n,H i n→ Rooted (p i) (F i n-L i) (b*e.η i n))
lemma corner {Y:ℕ→Field ι X} (h: Balance.Stable e H p F) (hw:∀ i,∀ᶠ N in atTop,H i N)(hl:∀ i x,Tendsto (fun j=> F i j x) atTop (𝓝 (Y i x))) : Stone e p H F Y:= by
   obtain ⟨⟨t,Ht,hP⟩,z,hZ,HZ⟩:= h; refine ⟨hl,⟨_,Ht.add hZ,fun i=> ?_⟩⟩; refine ⟨(accrued ((hw i).mono fun n h=> hP i n h) (hl i)).weaken (fun _=>le_rfl) (le_add_of_nonneg_right (hZ.bank i)), fun n hn=>?_ ⟩; have he:∀ᶠ m in atTop, Rooted (p i) (F i n-F i m) (z i *e.η i n):= ((hw i).and (eventually_ge_atTop n)).mono fun m h=> (by simpa only [min_eq_left h.2] using HZ i n m hn h.1); exact (accrued he (fun x=> tendsto_const_nhds.sub (hl i x))).weaken (fun _=>le_rfl) (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (Ht.bank _)) (e.η_pos ..).le)
variable (e)(x:G.ColorIndex)(E:∀ n,RackCore e.a e.M n)(V Y:ℕ→bore G)
structure Palm (V Y:ℕ→bore G): Prop where
   p i r k : 3≤k → Stone e (e.Bx k) Nat.le (fun v n=>e.incident x E v n i r) (fun v=> V v i r)
   q i r k : 3≤k → Stone e (e.Bx k) Nat.lt (fun v n=>e.entry x E v n i r) (fun v=> Y v i r)
lemma trees : ∃ V Y:ℕ→ bore G,e.Palm x E V Y:= by
   have hp:= e.rentLaw x E 3 le_rfl; let A:= Node (Dye G); have hx i r v (p:Fin r→A): (∃ y, Tendsto (fun n=> e.incident x E v n i r p) atTop (𝓝 y)) ∧ ∃ y, Tendsto (fun n=>e.entry x E v n i r p) atTop (𝓝 y):= by
      by_cases h:r=0; swap; · letI: NeZero r:= ⟨h⟩; exact ⟨point (hp i r).law.2 eventually_ge_atTop v p, point (hp i r).raw.2 eventually_gt_atTop v p⟩
      subst r; refine ⟨⟨0,?_⟩,0,?_⟩; · apply Tendsto.congr' _ (tendsto_const_nhds (x:=0)); filter_upwards [eventually_ge_atTop v] with n hv; exact (congr_fun ((e.wild x E _ _ hv).blazing.frame.scalar i) _).symm
      apply Tendsto.congr' _ (tendsto_const_nhds (x:=0)); filter_upwards [eventually_gt_atTop v] with n hv; exact (congr_fun ((e.forbes x E _ _ hv).honest.frame.scalar i) _).symm
   choose V hV using fun i r v p=> (hx i r v p).1; choose Z hZ using fun i r v p=> (hx i r v p).2; exact ⟨fun v i r p=> V i r v p,fun v i r p=> Z i r v p, ⟨fun i r k ht=>corner (e.rentLaw x E k ht i r).law eventually_ge_atTop (hV i r),fun i r k ht=> corner (e.rentLaw x E k ht i r).raw eventually_gt_atTop (hZ i r)⟩⟩
end Oasis
open Lattice RG Wilson Precision Org Pulse Pulse.Spine Spec Contacts.Solstice PhysicalNext.Repeat.Legato Milling
noncomputable def coordinate (u:Passage G)(h:Mirage u.M.K u.A.B.a u.M.O)(s:G.Simple): Oasis G:= ⟨u.M.K,u.A.B.a,u.M.O,u.A.B.M, h,u.A.B.plan,s,u.M.oga⟩
theorem borePalm (G:Gauge)(s:G.Simple){b:ℝ}(hx:0<b)(t:BidTri G)(F:Extraction.Order): ∃ u:Passage G, admits t u ∧ u.Z.path.levels.clock.kernel.penalty=b ∧
   (∃ h:Mirage u.M.K u.A.B.a u.M.O, ∃ (G':Garnet u) (V Y:ℕ→ bore G), let e:= coordinate u h s; e.Palm G'.x G'.E V Y) ∧ ∃ (g:Extraction.Order)(A:Table u.Z.book)(Z:Final u.Z (F.refine g) A) (M: Devices Z.sector.derivatives), MultipleLight Z M ∧ Nonempty (Transport.SystemBasis M) ∧ Nonempty (Thresholds M):= by
   obtain ⟨u,h,hq,⟨G'⟩,X⟩:= bore_path G s hx (bonus t) F; let hv:=(grants h); obtain ⟨V,Y,hh⟩:= (coordinate u hv.2 s).trees G'.x G'.E; exact ⟨u,hv.1,hq,⟨hv.2,G', V,Y,hh⟩,X⟩
end Reserve
end
end YM.Contacts.Barrage
