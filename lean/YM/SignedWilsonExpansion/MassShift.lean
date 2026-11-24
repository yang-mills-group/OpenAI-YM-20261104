import YM.SignedWilsonExpansion.MarkTop
namespace YM.SignedWilsonExpansion.MassShift
/-! # Order-two dilation operations on high kernels
This is a real stamp difference, at fixed high-cut parameter `t`. In particular it retains the counterterm response. -/
set_option autoImplicit false
noncomputable section
open Function Set Filter MeasureTheory Finset
open MS MS.Menus MS.Local.Physical MS.Land MS.Book MS.Landau MS.Landau.Detect MS.Koszul MS.Plane MS.Plane.Flux MS.High MS.Plane.Domain MS.Plane.Wire MS.Pearl MS.Outlook MS.Emit MS.Garment MS.Heat MS.Rake
open HighRank HighScale TreeLine TreeView LocalForm MarkRows
open scoped Classical Topology ContDiff BigOperators
variable {G:Gauge}
variable {V A D : Reading G} {u:ℝ} {r:ℕ} {d:ℤ} {b: Bool}
def bump (z:ℝ) (V:Reading G): Reading G := fun x=> V (x.1+z,x.2)
def leap (z:ℝ) (V:Reading G): Reading G := bump z V - V
lemma gap (w:Legs (Lane4 G))(track:Track b V D (ray w))(s:Clock ℝ)(hw:Course b w) : HasDerivAt (fun t=> leap u V (s.1,t) w) (leap u D s w) s.2:= (time_derivative w track hw (s.1+u) s.2).sub (time_derivative w track hw s.1 s.2)
lemma verges (z:ℝ)(H: Covariant V b r d): Covariant (leap z V) b r d:= by
  apply covariant_sub _ H; intro s t u w h hp; let V:=H (s+z) t u w h hp; unfold bump; rw [V]; congr 3; ring
lemma stampShift {E:Type}[AddCommGroup E][Module ℝ E]{f:ℝ→E} (flags:MS.Logarithm.Ready f) (v:ℝ): MS.Logarithm.Ready (fun x=>f (x+v)):= by
    refine flags.Ind (p:=fun f=>MS.Logarithm.Ready fun x=> f (x+v)) ?_ Logarithm.Ready.zero (fun i j a b=> a.add b) (fun c _ h=> h.scale c)
    intro a t; have he (i:ℝ):Polynomial.eval i (Polynomial.X + Polynomial.C v)=i+v:=by rw [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C];
    convert Logarithm.status (a.comp (Polynomial.X+Polynomial.C v)) t using 1; funext x; change a.eval (x+v) • t = _; rw [Polynomial.eval_comp,he]
lemma stamp_shift (z:ℝ)(H:High.stamp V): High.stamp (leap z V):= (stampShift H z).sub H
lemma cycle_eq (K:TreeLine.Line G)(μ:Measure FourP){F H:Law G}{w:Legs (Lane4 G)}(hc:Course b w) (h:∀v,Course b v → v.length=w.length+2 → F v=H v): cycle K μ F w=cycle K μ H w:= by
    unfold cycle; apply integral_congr_ae; filter_upwards with i; rw [at_trc,at_trc]; exact sum_congr rfl fun a _=> sum_congr rfl fun b _=> by rw [h ((a,i)::(b,-i)::w) (fun v=>by simp [hc v]) (by simp)]
local notation "Kx" => spaceD G
variable {B : Deck G}{M:Booked B}(S:MS_Data G M)(simple:G.Simple)
local notation "A2" => bulkD S
local notation "Wκ" => Archive 4 S.bulk
local notation "qS" => degreeMaster id Kx
local notation "κ" => ((2:ℂ)⁻¹)
include simple
lemma bulk_peers (v:ℝ)(t:Clock ℝ) (w:Legs (Lane4 G))(h:Course true w)(hp:w.length=2) (D:Needle G):
    leap v (recu D 1 κ Wκ Wκ 2) t w=0 := by
  let a:Clock ℝ:=(t.1+v,t.2)
  have cv : cycle (D.meter t.2) D.measure (A2 t) w = cycle (D.meter t.2) D.measure (A2 a) w:= cycle_eq _ _ h fun i hi hx=> Eq.trans (BulkTop.pulse S t i hi (by omega)) ((BulkTop.pulse S a i hi (by omega)).symm)
  have stop {i:Clock ℝ}:D.using_tree 2 1 κ (fun j=>Wκ j i) (fun j=>Wκ j i) i.2 D.meter w=0:= by
    rw [tree_two,Pi.smul_apply,tree_height _ _ _ w true h,smul_zero]
    intro n m hx; have hs a (hv:a ≠ 3) (w' :Legs (Lane4 G))(H:net w'=0)(ha:w'.length=a)(hn:a>0): Wκ 1 i w'=0:= by rw [BulkTop.paid1 S simple _ w' (by omega) H]; exact BulkTop.bulk1_r (G:=G) 0 w' (by rw [mod_int]; omega)
    by_cases hh:n=2
    · right; intro w hw h; exact hs _ (by omega) w (hw rfl) h (by omega)
    left; intro w hw h; exact hs _ (by omega) w hw h (by omega)
  change _-_= (0:ℂ)
  change (recu D 1 κ _ _ 2 a w)-(recu D 1 κ _ _ 2 t w)=0
  unfold recu; simp only [Pi.add_apply, stop]; rw [cv]; exact sub_self _
lemma bulk_tri : Static A2 3 4 true:= by
  refine (bulkView S 2 (by omega)).static (fun _=>by decide) (fun t w hw he=> bulk_height S _ _ hw (by omega)) ?_
  intro t w h he; rw [HighRank.tree_two,Pi.smul_apply,tree_height _ _ _ _ true h,smul_zero]; intro i j ht; have hs a (hv:a≠3)(w' :Legs (Lane4 G))(H:net w'=0)(ha:w'.length=a)(hn:a>0): Wκ 1 t w'=0:= by rw [BulkTop.paid1 S simple _ w' (by omega) H]; exact BulkTop.bulk1_r (G:=G) 0 w' (by rw [mod_int]; omega)
  by_cases hv:i=2; · exact Or.inr fun w' hx hl=> hs _ (by omega) _ (hx rfl) hl (by omega)
  exact Or.inl fun w' hx hl=> hs _ (by omega) _ hx hl (by omega)
lemma lonely (v:ℝ)(t:Clock ℝ)(w:Legs (Lane4 G))(h:Course true w)(hp:0<w.length)(hh:w.length≠2) : leap v A2 t w=0:= by
  obtain hv|hv:= lt_or_gt_of_ne hh
  · obtain ⟨i,rfl⟩:= List.length_eq_one_iff.mp (show w.length=1 from by omega); exact sub_eq_zero.mpr ((bulk_single S 2 _ _ (h rfl) simple).trans (bulk_single S 2 _ _ (h rfl) simple).symm)
  unfold leap bump; refine sub_eq_zero.mpr ?_ -- Pi issue
  rcases lt_or_eq_of_le (show 3≤w.length from by omega) with hh|hh; swap; exact (bulk_tri S simple).same _ _ _ _ w h hh.symm
  rcases lt_or_eq_of_le (show 4≤w.length from by omega) with ht|ht; exact ((bulk_height S _ _ h ht).trans (bulk_height S _ _ h ht).symm)
  exact (BulkTop.pulse S (t.1+v,t.2) w h ht.symm).trans (BulkTop.pulse S t w h ht.symm).symm

lemma static_b (v:ℝ):Static (leap v A2) 2 4 true:= by
  let A:=Outlook.dock S.bulkOK MS.Motif.wisdom
  refine static_of ?_ (verges _ (fun _ _ _ _ _ _=>congr_fun (Port.Bx4 (bulkView S 2 (by norm_num)|>.host)) _)) ?_ (stamp_shift _ (A.master.poly 2))
  · intro y t w h hw; rw [←bulk_peers S simple v (y,t) w h hw]; exact gap w (A.master.road ℝ (ray w) 2 (by omega) (by rw [Used];intro; simp [hw])) (y,t) h
  intro E i j w hc he ⟨t,y⟩; have hx z:= Outlook.hair (bulkView S 2 (by omega)|>.host) (n:=0) (w:=w) (s:=y) (y:=z); exact (hx (t+v)).sub (hx t) -- names

lemma bulk_q (v:ℝ)(t:Clock ℝ)(w:Legs (Lane4 G))(h:Course true w)(hp:w.length=2) : natQ (leap v A2 t) w=0:= by
  let A:=Outlook.dock S.bulkOK MS.Motif.wisdom
  have eq s:=A.master.qfm 2 s w (by norm_num) (fun _=>by omega) h
  unfold natQ leap bump; rw [Pi.sub_apply,map_sub,Pi.sub_apply]
  change ((send id).raise (Wκ 2 _) w)-((send id).raise (Wκ 2 t) w)= _
  rw [eq,eq]; have ht:=bulk_peers S simple v t w h hp (qS); unfold Ward; simp only [Pi.neg_apply,neg_sub_neg]; exact (sub_eq_zero.mpr (sub_eq_zero.mp ht).symm)
lemma bulk_class (v:ℝ)(t:Clock ℝ): Class (Book.mask 2 (leap v A2 t)) 4 := by
  let F:=leap v A2 t; let s:=(t.1+v,t.2); let P:= Outlook.dock S.bulkOK MS.Motif.wisdom
  refine ⟨(solid_level ((P.master.trueC 2 s).sub (P.master.trueC 2 t)) (2:ℤ)),?_, masked _ (static_b S simple v) t,?_⟩
  · intro w h; rw [show natQ (mask 2 F)=mask 2 (natQ F) from (MS.Lifting.mask_raises id _ 2).symm]; by_cases hv:w.length=2; · rw [Book.enough _ (by omega)]; exact bulk_q S simple _ _ _ (fun _=> h) hv
    exact Book.strange _ (by omega)
  intro k w h; have hv: SignedScope true F:= (P.master.reflects 2 s rfl).sub (P.master.reflects 2 t rfl); by_cases hx:w.length=2; · rw [Book.enough _ (by simp [hx]),Book.enough _ (by omega)]; exact hv k w h
  rw [Book.strange _ (by simp only [List.length_map]; omega), Book.strange _ (by omega),mul_zero]
lemma propagation (v:ℝ) : ∃ a b:ℝ,∀ t:Clock ℝ,∀ w:Legs (Lane4 G),Course true w → 0<w.length → leap v A2 t w=ranktwo (G:=G) a b w:= by
  obtain ⟨a,b,_,eq⟩:= pair_class (bulk_class S simple v (0,0)) simple (le_refl 4)
  refine ⟨a,b,fun t w he hw=>?_⟩; by_cases hh:w.length=2
  · have h:=eq w (he rfl) hh; rw [Book.enough _ (by omega)] at h; exact ((static_b S simple v).same _ _ _ _ w he hh).trans h
  rw [lonely S simple _ _ _ he hw hh]
  rcases w with _|⟨i,_|⟨j,_|k⟩⟩; exacts [False.elim ((Nat.lt_irrefl _) hw),rfl,(hh rfl).elim,rfl]
end
end YM.SignedWilsonExpansion.MassShift
