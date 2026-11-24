import YM.RegulatorIR.Cluster.Time
import YM.RegulatorIR.Step.Horizontal

/-! Offer, endHeat and deterministic transfer respect the conventions.
Heating + packaging of the absolute difference sees clash. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Cluster
open MvPolynomial Function Budget Budget.Packet Budget.Layer Budget.Tuple Diagram Step Uniform Gradient Train Finset Filter Brief
open scoped BigOperators Topology ENNReal NNReal Classical
variable {X Y Z:Type}{r s t u m n a b p k e:ℕ}
def present (f:X↪Y)(T:Orders X): Orders Y:= fun e i=>offer f (T e i)
lemma ticket_offer (f:X↪Y)(T U:Orders X) : present f (accord T U)=accord (present f T) (present f U):=by
 ext1 e;ext1 r; ext1 x; by_cases he:x ∈ Set.range (acrossT f)
 · obtain ⟨v,rfl⟩:=he; rw [present, offer_eq]
   have hp (T:Orders X)(e r): crop f ((present f T) e r)=T e r:= funext (fun y=> offer_eq f ..)
   change _= crop f (accord (present f T) (present f U) e r) v;rw [crop_orders]; simp_rw [hp]
 rw [present, offer_zero f he]; symm; simp_rw [accord, Finset.sum_apply,crisp,Finset.sum_apply]
 apply sum_eq_zero; intro i _; apply sum_eq_zero; intro j hj
 have hh:=mem_antidiagonal.mp hj; subst r; simp only [pie]; change (symmetry _) x=0; rw [symmetry_at]; apply mul_eq_zero_of_right; apply sum_eq_zero; intro u _
 let z:= x ∘ u; let I:=cutLeft (r:=j.1) z; let J:=cutRight (s:=j.2) z
 have h' : ¬ (I ∈ Set.range (acrossT f) ∧ J ∈ Set.range (acrossT f)):=by
    rintro ⟨⟨q,hq⟩,⟨v,hv⟩⟩
    have hx : acrossT f (Fin.append q v)=z:=(Tuple.comp_append (f:X→Y) q v).trans (by change Fin.append (acrossT f q) (acrossT f v)=_; rw [hq,hv]; exact recombine ..)
    apply he; refine ⟨Fin.append q v ∘ u.symm,?_⟩; ext1 a; change acrossT f (Fin.append q v) (u.symm a)=_; rw [hx]; simp [z]
 change offer f _ I * offer f _ J=0
 by_cases h:I∈ Set.range (acrossT f)
 · rw [offer_zero f (fun he=> h' ⟨h,he⟩),mul_zero]
 rw [offer_zero f h,zero_mul]
lemma ranks_offer (f:X↪Y)(T:Orders X)(h:Ranks m T): Ranks m (present f T):=fun i r he=>h i r (fun hv=> he (by unfold present;rw [hv];ext1 x; simp [offer,Stalk.collect]))
lemma sym_offer (f:X↪Y)(T:Orders X)(h:gradedSymmetric T): gradedSymmetric (present f T):=fun i r=>offer_symm f _ (h i r)
lemma end_ranks {K:Layer X X}(m:ℕ){V T:Orders X}(b:Bool)(h:Ranks m T)(hh:Vacuum V) : Ranks m (endHeat m K (logHeat K V b) T):= heated_ranks _ (fun k e r hv=>(marked_cap m K V hh T h b e r k hv).1) _
lemma end_sym {K:Layer X X}(m:ℕ)(V:Rhythm X){T:Orders X}(h:gradedSymmetric T) : gradedSymmetric (endHeat m K V T):= heated_sym _ (fun k=> markedSym K V h k) _

lemma inert_price (g:Y↪X){K:Layer X X}{c:ℝ≥0∞}(hc:c≠⊤)(hh:height K c): CostRow (inert (Embedding.refl X) g K) p:=fun i _=>⟨_,hc,fun x y=>by unfold inert; split_ifs; exact hh ..; rw [enorm_zero]; exact bot_le⟩
lemma venue (g:Y↪X){K:Layer X X}{c:ℝ≥0∞}(hc:c≠⊤)(hh:height K c)(T:Orders X)(h:quota (T e r) 1≠⊤): shot (inert (Embedding.refl X) g K) T e r= crop g (draft K (T e r)):=by
 let f:= Embedding.refl X
 rw [blankShot _ (inert_b f g K), carriage f g K (T e r) (inert_d f g K) h hh hc]
 rw [show offer f (T e r)=T e r from funext (fun z=>offer_eq f _ z)]
lemma provision (g:Y↪X){K:Layer X X}{c:ℝ≥0∞}(hc:c≠⊤)(hh:height K c)(T U:Orders X)(ht:Bill T e)(hu:Bill U e)(hA:Ranks a T)(hB:Ranks b U) : crop g (draft K (accord T U e r)) = accord (fun i j=>crop g (draft K (T i j))) (fun i j=> crop g (draft K (U i j))) e r:=by
 let Γ:= inert (Embedding.refl X) g K
 rw [← venue g hc hh (accord T U) (parent T U ht hu e le_rfl r), shot_product Γ (inert_price g hc hh) ht hu hA hB le_rfl]; unfold accord;apply sum_congr rfl; intro i hi
 have H:= mem_antidiagonal.mp hi
 exact congr_arg₂ (fun t u : Ranked Y=>crisp t u r) (funext (fun j=>venue g hc hh T (ht i.1 (by omega) j))) (funext (fun j=>venue g hc hh U (hu i.2 (by omega) j)))
lemma draft_minor (K:Layer X X){c:ℝ≥0∞}(hc:c≠⊤)(hh:height K c)(T U:Packet X r)(h:quota T 1≠⊤)(hx:quota U 1≠⊤): draft K (T-U)=draft K T-draft K U:=by
 rw [draft,draft,draft,← symmetry_sub]; apply congr_arg;ext1 x
 let p:=List.finRange r
 let f:=Gradient.field T K x p; let g:= Gradient.field U K x p
 rw [Pi.sub_apply,ray_assembly (T-U) _ _ _ hh (ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨h,hx⟩) (quota_sub ..)) hc (List.nodup_finRange _),ray_assembly T _ _ _ hh h hc (List.nodup_finRange _),ray_assembly U _ _ _ hh hx hc (List.nodup_finRange _),← (field_sum T K x p hh hc h).tsum_sub (field_sum U K x p hh hc hx)]
 apply tsum_congr; intro i; unfold Gradient.field; split_ifs
 · exact sub_mul ..
 simp
end YM.RegulatorIR.Cluster
