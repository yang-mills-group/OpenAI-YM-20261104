import YM.FormalBulk08.Annex.Cube
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Annex
open Function Filter Lattice Dawn Set
open scoped BigOperators Topology ENNReal Classical ContDiff
variable {D:ℕ}
lemma beam_small (x:E4)(h:x∈beam): ‖x‖ ≤ 8:= by
   have he: ‖∑ i:Axis, x i • basis i‖≤ ∑ _i:Axis,(1/2:ℝ) := by
      apply (norm_sum_le ..).trans; apply Finset.sum_le_sum; intro i _; rw [norm_smul,basis_norm,mul_one]; exact cube_test.mp h i
   rw [basic4] at he; exact he.trans (by norm_num [Axis])
lemma beam_closed : IsClosed beam := by
   have hx : beam= ⋂ i: Axis,{x:E4| |x i|≤1/2} := by ext x; simp only [cube_test,mem_iInter,mem_setOf]
   rw [hx]; exact isClosed_iInter fun i=> isClosed_le (shadeP i).continuous.abs continuous_const
abbrev Deck:= ↥beam
def embark (p:Deck): Pier:= ⟨p.val,by rw [Metric.mem_closedBall,dist_zero_right];exact beam_small _ p.property⟩
lemma embarks : Continuous embark:= Continuous.subtype_mk continuous_subtype_val _
instance deckComp : CompactSpace Deck:= isCompact_iff_compactSpace.mp ((isCompact_closedBall (0:E4) 8).of_isClosed_subset beam_closed (fun x hx=> Metric.mem_closedBall.mpr (by rw [dist_zero_right];exact beam_small _ hx)))
instance deckNE:Nonempty Deck:= ⟨0,(cube_test).mpr (fun _=>by simp)⟩

abbrev LotusD (D:ℕ):= Brush D → C(Deck,ℝ)
def compress (D:ℕ): Studio D→ₗ[ℝ]LotusD D where
    toFun f k := ⟨(f.val k)∘embark,(f.val k).continuous.comp embarks⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
lemma compel (p:Studio D)(k:Brush D)(x:Deck): compress D p k x=p.val k (embark x):=rfl
lemma comp_le (p:Studio D): ‖compress D p‖ ≤ ‖p‖:= (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (fun k => (ContinuousMap.norm_le _ (norm_nonneg _)).mpr (fun x=>le_panel p k (embark x)))
-- Λ_k test cost buys extension constant
lemma supported (D:ℕ) : ∃ C:ℝ,0≤ C∧∀ x:Studio D,∃ p: Studio D, compress D x=compress D p ∧ ‖p‖≤ C*‖compress D x‖:= by
   obtain ⟨C,c,J⟩:=cube_eq D; refine ⟨C,c,fun x=>?_⟩; obtain ⟨p,rfl⟩:= portrayed D x; let A:= (compress D) (portrait D p); obtain ⟨g,H⟩:= J p ‖A‖ (norm_nonneg _) (fun x hx k=> le_trans (b:=‖A k‖) ((A k).norm_coe_le_norm ⟨x,hx⟩) (norm_le_pi_norm ..))
   refine ⟨portrait D g,?_,panel_le _ (by positivity) ?_⟩
   · ext1 i; ext1 f; exact (H.meets f.val f.property i).symm
   intro i x; apply H.pays x.val _ i; refine cloud_has.mpr ⟨fun k:Axis=>?_ ,by simp⟩
   calc
       |x.val k|≤‖x.val‖:= by simpa using (abs_real_inner_le_norm (basis k) x.val)
       _≤8:= still _
lemma peninsula_in (L:Side)(hp:Odd L.val)(h:2≤L.val)(x:Site L)(f:Deck): (Dawn.peninsula x h (embark f)).val ∈ beam := by
   apply cube_test.mpr; intro i; obtain ⟨u,v⟩:=abs_le.mp (cube_test.mp f.property i); change |bay x f.val i| ≤1/2; unfold bay pith; simp only [PiLp.smul_apply,PiLp.add_apply,smul_eq_mul,Planned.PrimaryIntegral295.Place.seat_apply]
   obtain ht:=lift_centers x i; have hs (j:ℕ) : (0:ℝ)≤j:=Nat.cast_nonneg _
   have hl: -(L.val:ℝ)+1 ≤ 2 * lift x i := by exact_mod_cast (show -(L.val:ℤ)+1 ≤ 2*lift x i by omega)
   have hv: 2*(lift x i :ℤ) ≤ (L.val:ℝ)-1:= by exact_mod_cast (show 2*lift x i ≤(L.val:ℤ)-1 by obtain ⟨V,h⟩:=hp;omega)
   have hL:scale L*(L.val:ℝ)=1:=by unfold scale;field_simp
   have h:=@scale_pos L
   rw [abs_le]; constructor<;> nlinarith
lemma pen_keeps {L:Side}(hp:Odd L.val)(h:2≤L.val)(x:Site L)(p u: Studio D)(hx:compress D p=compress D u): compress D (throughW x D h p)=compress D (throughW x D h u) := by
   ext1 k;ext1 f;rw [compel,compel]; change (tunnel x D h p).val k _= (tunnel x D h u).val k _; rw [tunnel_show,tunnel_show]; exact congr_arg (_ * ·) (DFunLike.congr_fun (congr_fun hx k) ⟨_,peninsula_in L hp h x f⟩)
lemma notch_holds {a:Seasons}{p q:Studio D}(hp:Chapel.upper a ≤ D)(h: compress D p=compress D q): notch a hp p=notch a hp q:=DFunLike.congr_fun (congr_fun h (finger hp)) (⟨0,(cube_test).mpr (fun _=>by simp)⟩:Deck)
end YM.FormalBulk08.Annex
