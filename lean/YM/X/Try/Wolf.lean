import YM.X.Try.Hoop
/-!
# High symbol estimates in precision grade d+1, NOT polished; automatic from slot number. Uses W references restored, cut filtration, applies through all headings.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Tri
open Lattice Wilson Next.Rank Normal LiftMark Configuration MvPolynomial Function Filter Set Asymptotics Gauge
open Source PertExtension LatticePT Braid Gauss ProjectorNext.Calibration Bid Hue Grow Clove
open Stems hiding X
open Heat.Top
open Jet hiding Word
open scoped Topology ContDiff BigOperators Pointwise Classical
variable {G:Gauge} {d n k:ℕ} {V I:Type*} {F : Labels.Frame G n}{H : Source.Hol G} {S: Source.SectionData F} -- name
local notation "K"=> Atom G
local notation "Z"=> Curly G
lemma HCne {p:poly V}(h:HC p d)(e:n≠d): cut n p=0:= h.weightedHomogeneousComponent_ne _ e
lemma orchestra (F: V→Atom G)(x: Brush G)(p:poly V)(h:Strong (fun _=>1) d p) :
     Plain (festival x (rename F p)) d (snap x (loom (rename F (cut d p)))) (snap x (call loom delve (rename F (cut d p))+ loom (rename F (cut (d+1) p)))):= by
     let u:= (festival x).comp (rename F); let L:= (snap x).comp (loom.comp (rename F)); let L':= (snap x).toLinearMap ∘ₗ call loom delve ∘ₗ (rename F).toLinearMap; let Y:= L'.comp (cut d) + L.toLinearMap.comp (cut (d+1)); let A:= L.toLinearMap.comp (cut d); rw [map_add]; change Plain (u p) d (A p) (Y p); rw [p.as_sum,map_sum,map_sum,map_sum]; refine Plain.collect _ (fun i hi=>?_); let t:= Heat.Top.degree i; have ht:HC (monomial i (coeff i p)) t:= isWeightedHomogeneous_monomial _ _ _ rfl; let Z₀:= monomial i (coeff i p); have he: Plain (u Z₀) t (L Z₀) (L' Z₀):= ceremony F x Z₀ ht
     change Plain (u Z₀) _ (L (cut d Z₀)) (L' (cut d Z₀) + L (cut (d+1) Z₀)); rcases lt_or_eq_of_le (sturdy.mp h i hi) with hk|hk;
     · rw [HCne (p:=Z₀) ht hk.ne, map_zero,map_zero,zero_add]; have hh:=he.offset (n:=d) hk; split_ifs at hh with hg; · rw [show cut (d+1) Z₀= Z₀ from hg.symm ▸ leafy.mp ht]; exact hh
       rw [HCne (p:=Z₀) ht hg,map_zero]; exact hh
     change d=t at hk; rw [hk]; rw [leafy (p:=Z₀)|>.mp ht,HCne (p:=Z₀) (n:=t+1) ht (by omega), map_zero, add_zero]; exact he
lemma festive (x: Brush G)(p:poly K)(t:ℝ): festival x p t= aeval (fun i:K=> Complex.ofReal (SlotV i (posit (t • x)))) p:= by
     refine DFunLike.congr_fun (f:= (Pi.evalAlgHom ℂ _ t).comp (festival x)) ?_ p; ext1; simp only [AlgHom.comp_apply,festival,aeval_X]; rfl
section
variable (h:S.Sound H)(P:pop S) (i:F.Index)
def trumpet (k:ℕ)(i:F.Index): poly K:= Heat.Top.rawPart ((rendered S P).columns i) ((rendered S P).shape i) k
lemma pop_HC (k:ℕ): HC (Tri.trumpet P k i) k:= by
    unfold Tri.trumpet Heat.Top.rawPart; rw [leafy,cut_relabel]; apply congr_arg; exact weightedHomogeneousComponent_mem ..|>.weightedHomogeneousComponent_same
lemma assemb (x:Brush G): let k:=(F.grades i).2; snap x (mark (evalS S i) (opt i h P) (k+1))= snap x (call Stems.loom delve (Tri.trumpet P k i)+loom (Tri.trumpet P (k+1) i)) := by
    intro k; rw [mark_test]; let R:= (rendered S P); let B:= R.columns i; let U:= R.shape i; let g:= fun v:Fin (R.count i) × G.ColorIndex=> ((B v.1,v.2): Atom G); let p:= along (evalS S i) x
    have he1 : Complex.ofRealCLM ∘ p= festival x (rename g U):= by funext r; rw [festive,aeval_rename]; change Complex.ofReal (evalS S i _) = _; rw [eval_true i h _, rend_acts h P i]; rfl
    have hP:= orchestra g x U (d:=k) ?_
    swap
    · apply sturdy.mpr; intro z hz; change k≤ Heat.Top.degree z; rw [Heat.Top.degree_eq]; exact R.low i z hz -- direction
    rw [← he1] at hP; have hy := (Act.linear (L:=Complex.ofRealCLM) (show Act (k+1) p (someJ p) from ⟨along_zero (opt i h P) x,fun _ _=>rfl⟩)).writes (k+1) le_rfl
    exact hy.symm.trans hP.awake
lemma basis_stones : let k:=(F.grades i).2; Stone ⊤ (2*k) (mark (evalS S i) (opt i h P) (k+1)) (call dialF glove (lump (Tri.trumpet P k i))):= by
    intro k; rw [snap_ext (fun x=> assemb h P i x), lump, ← call_rename dialF glove drop];
    nth_rw 2 [← add_zero (call _ _ _)]; -- nested wrong
    refine (call_stone loom _ ⊤ _ (pop_HC P i k) (fun i=> (stone_arc i).tier le_top) (fun i=> slot_stone i)).add (Stone.quiet ?_) -- implicit rank
    refine weaken_v (n:=2*(k+1)) ?_ ?_ -- inspect
    · omega
    apply tier_v (show Reed.Horizontal G ≤⊤ from le_top); exact Stone.sta (stoneF (pop_HC P i (k+1)))
end
variable (p:Word G)
def thought (i:p.F.Index):= (topMatrix p.S p.H p.sound p.chosen).basis i
def lody (p:Word G):= (p.F.grades p.axis).2
-- high slot number d = d/2
lemma sum_stone (ht:p.d=2*d) : Stone ⊤ p.d (cut (d+1) (bookMark p 1)) (call dialF glove (lump (cut d (baseMark p)))):= by
     simp only [baseMark,bookMark,Vertex.combination,map_sum,map_smul]; apply Stone.sums; intro i _; refine Stone.scalp _ ?_; let v:= (p.F.grades i).2; have hv:HC (hut 1 p i) (v+1):= markHC _ (opt i p.sound p.chosen); have he:v≤d:= by have hx:=slotCount i; have hy:= p.F.bound i; unfold v; omega
     let B:= thought p i; have hk: B=Tri.trumpet p.chosen v i:= rfl; have hB : HC B v:= by rw [hk]; exact pop_HC p.chosen ..
     change Stone (⊤:Submodule ℝ (Reed.Fan G)) p.d (cut (d+1) _) (call _ _ (lump (cut _ B)))
     rcases lt_or_eq_of_le he with he|he
     · rw [HCne (n:=d+1) hv (by omega),HCne (n:=d) hB (by omega),map_zero,map_zero]; exact Stone.quiet (Submodule.zero_mem _)
     rw [←he,leafy.mp hv,leafy.mp hB]; nth_rw 1 [ht,← he]; exact basis_stones p.sound p.chosen i
lemma base_rank (ht:p.d=2*d): Plate.duty (baseMark p) d:= by unfold baseMark Vertex.combination; refine Plate.duty.costs _ (fun i _=> Plate.duty.scalar _ (le_trans ((topMatrix ..).bound _) ?_)); change (p.F.grades _).2≤d; have h:= slotCount i; have hx:= p.F.bound i; omega
lemma cut_looks (ht:p.d=2*d): cut d (looking p)=loom (cut d (baseMark p)):= by rw [looking, cut_loom,Vertex.normalized]; exact congr_arg loom (cut_thermal (covarianceSymbol G) _ (base_rank p ht)) -- .
lemma initial_look (ht:p.d=2*d)(hp:lody p=d): Stone (Reed.Horizontal G) (p.d) (looking p) (dialF (lump (cut d (baseMark p)))):= by
   let v:= world p.d p; let V₀:=level Configuration.bear p.d (world p.d p); have h: level Configuration.bear p.d (v-cut d v)=0:= by
       rw [map_sub, show level Configuration.bear p.d (cut d v)=cut d V₀ from ?_]; swap
       · unfold V₀; ext i; change coeff i (Rise.trim _ _ _) = coeff i (cut _ (Rise.trim _ _ _)); simp only [Rise.trim_coeff,cut_coeff]; split_ifs <;> rfl
       apply sub_eq_zero.mpr; apply Eq.symm; unfold V₀; rw [restored p (Nat.le_refl _),cut_relabel]; apply congr_arg; let L0:=Labels.raiseLabel G (Nat.le_refl p.d) (labelledP p); apply leafy.mp (Grow.hom_feed (boundKey G p.d) (w:=fun _=>1) ?_ (p:= L0.val) (u:=fun _=>1) ?_)
       · intro i; rw [boundKey,aeval_X]; split
         · exact isWeightedHomogeneous_X ..
         exact isWeightedHomogeneous_zero ..
       exact hp ▸ labelHC (k:=(p.F.grades p.axis).1) (p.F.basis p.axis) (p.F.pure p.axis)
   have hu: looking p - cut d (looking p) ∈ verse (Reed.Horizontal G) (p.d+1):= by
      rw [← loom_eq p.d, assignP,cut_swap, ← map_sub]; refine layer_sub Configuration.bear _ _ (Strong.undo h) ?_ -- map
      intro i; rw [exchange_x]; rw [show Configuration.bear i= Configuration.bear i-1+1 from ((by have := plus₁ i; omega))]; exact verse_glyph (Reed.occ Heat.Ray.address p.d i) (Reed.omen Heat.Ray.address p.d i)
   rw [cut_looks p ht] at hu; refine Stone.compose (p':=_) ⟨?_,hu⟩ ?_
   · exact (ht.symm ▸ stoneF (p:=cut d (baseMark p)) (d:=d) (weightedHomogeneousComponent_mem ..)).sta
   exact ht.symm ▸ stoneF (p:=cut d (baseMark p)) (d:=d) (weightedHomogeneousComponent_mem ..)
end YM.PositionX.Tri
