import YM.SignedWilsonExpansion.Radial
namespace YM.SignedWilsonExpansion.OrderHigh
/-! Replay pricing into the unequal scales **actual** position on `MS`;
not assume a flat field beta convention. -/
set_option autoImplicit false
noncomputable section
open Function Set Filter MeasureTheory Finset
open MS MS.Menus MS.Local.Physical MS.Land MS.Book MS.Landau MS.Landau.Detect MS.Koszul MS.Plane MS.Plane.Flux MS.High MS.Plane.Domain MS.Plane.Wire MS.Pearl MS.Outlook MS.Emit MS.Heat MS.Rake
open MS.Garment MS.Motif MS.Halo MS.Arts MS.Tone MS.City
open FVA2 FVA2.Lambda Area Walk Bubble TreeLine TreeView HighRank HighScale MarkRows AxisChoice MassShift MarkShift
open Gaussian
open scoped Classical Topology ContDiff BigOperators
variable {G:Gauge}
variable {B : Land.Booked (Press.portDeck G)}(M:MS_Data G B)(simple:G.Simple)
abbrev kinetic (G:Gauge) :ℝ:= (13/3)*G.casimir*b₀
abbrev locus (G:Gauge) : ℝ:= (-14/3)*G.casimir*b₀
variable (t v:ℝ)
local notation "m" => Energy.called 1 2 G
local notation "Tκ" => ((-8:ℝ) :ℂ)
local notation "M0" => Archive 4 M.bulk
local notation "FP" => recu (spaceD G) 0 1 M0 ( packet M m ) 2
include simple
lemma cashD (w:G.ColorIndex): HasDerivAt (fun t:ℝ=> torch 2 (bulkD M (t,0)) (Canvas.letters w)) ((kinetic G:ℝ):ℂ) t:= by
    obtain ht:= Canvas.fee (k:=2) (n:=2) M.bulkOK 0 ( Canvas.letters w ) ( fun _=>by simp [Canvas.letters,net,W,qnote]) (by simp [Canvas.letters]) (by decide) t rfl
    rw [ Lathe.project_w w simple M.bulkOK t, BranchR.walkW ] at ht; convert ht using 1; unfold kinetic; push_cast; ring
omit simple in
lemma difference (F:ℝ→ℂ)(c:ℂ)(h:∀ x,HasDerivAt F c x): F (t+v)- F t = v • c:= by
    let f (x:ℝ):= F x-x • c; have hr(x): HasDerivAt f (0:ℂ) x:= by convert! ((h x).sub ( (hasDerivAt_id' x).smul_const c )) using 1; simp
    have he:= is_const_of_deriv_eq_zero (fun i=> ( hr i ).differentiableAt ) (fun i=> (hr i).deriv) t (t+v)
    unfold f at he; rw [ add_smul ] at he; linear_combination (norm:=abel) -he -- sign?
lemma observe (w:G.ColorIndex): torch 2 ( leap v (M0 2) (0,0) ) (Canvas.letters w)=(↑(v*kinetic G):ℂ):= by
    let F(l:ℝ):= ( bulkD M (l,0) )
    change torch 2 ( F (0+v) -F 0 ) _=_
    have hx(z:ℝ): Polish (F z):= fun E _ _ a=> Outlook.hair (bulkView M 2 (by norm_num)|>.host) (n:=0) a
    rw [ High.Knobs.torch_sub (Canvas.letters w) ( hx _ _ _ ) ( hx _ _ _ ), difference 0 v (fun t=> torch 2 ( F t ) (Canvas.letters w)) ( kinetic G:ℂ ) (fun t=> cashD M simple t w) ]; exact (Complex.ofReal_mul ..).symm
-- order shift high fact applies WITH mark too. kinetic sector all partners
omit simple in
lemma stamp_static {d:ℤ}{r:ℕ}{b:Bool}{F:Reading G}(h:Static F r d b)(S:Clock ℝ)
    (w:Legs (Lane4 G))(hp:Course b w)(n:ℕ)(hx:w.length=r)(hv:fieldDim wfield w+n=d) : torch n ( F S ) w = F S w:= by
    let v:=F S; have hq: torch n v w=torch n (Book.mask r v) w:= by
       simp_rw [torch_at]; apply congr_arg; funext x; exact (Book.enough _ (by simp [hx])).symm
    rw [hq,(LocalForm.masked _ h S).const_term w hp, if_pos hv]; exact Book.enough _ (by rw [hx])

lemma propagation_E : ∃ b:ℝ,∀ t:Clock ℝ,∀ w:Legs (Lane4 G),Course true w → 0<w.length → leap v (bulkD M) t w=ranktwo (G:=G) (v*kinetic G) b w:= by
    obtain ⟨i⟩:= color_ne simple; obtain ⟨a,b,H⟩:= propagation M simple v
    refine ⟨ b,?_ ⟩; let t:Clock ℝ:=(0,0)
    suffices h:a=v*kinetic G from h ▸ H
    let w:= Canvas.letters i; have ht: Course true w:= fun _=> by simp [w,Canvas.letters,W,qnote,net]
    obtain he:= observe M simple v i
    rw [ stamp_static (static_b M simple v) (0,0) ( Canvas.letters i ) ht 2 rfl rfl,H t w ht (by change 0<2; decide) ] at he -- parser `H t w` conflict
    exact Complex.ofReal_injective (by simpa only [show ranktwo a b w=(a:ℂ) from (by unfold w Canvas.letters; simp [ranktwo,qnote,W,kinds,spray,Landau.precision, Pi.single_apply,Momentum.sq, ite_pow, Landau.delta] ) ] using he)

private lemma wall_p : Polish (wall M v):= by
    intro E _ _ w; by_cases he:w.length=2
    · have hx: fieldVal (wall M v) w=fieldVal (leap v (bulkD M) (0,0)) w:= funext fun x=> Book.enough _ (by simp [he])
      rw [hx]; exact (hair (bulkView M 2 (by omega)|>.host) (n:=0) (y:=0+v) (s:=0) w).sub (hair (bulkView M 2 (by omega)|>.host) (n:=0) (y:=0) (s:=0) w)
    rw [show fieldVal (wall M v) w=0 from funext fun x=> Book.strange _ (show ((sail w x).length:ℤ) ≠ 2 from by rw [sail_len]; omega)]; exact contDiff_const
lemma static_M : Static (settled M m v) 2 4 false:=
    bridge_static M m simple ( Energy.firstE 1 2 G 0 ) ( Energy.full ) v
lemma settle_bill (i j:Axis)(k:G.ColorIndex)(p q:FourP) :
    let w:=[W i k p,W j k q]
    torch 2 (settled M m v (0,0)) w=torch 2 ( packet M m 2 (0+v,0)) w - torch 2 (packet M m 2 (0,0)) w:= by
    intro w; let F:=bridge M m v 0; have he:TorchE.emptyR (fun t=>F (sail (ray w) t)):= by unfold F MarkShift.bridge; rw [Energy.found,Walk.ampL]; exact TorchE.skipH (wall_p M simple v) TorchE.smooth_amp
    let A z:=fieldVal ( packet M m 2 ( z,0 )) ( ray w ); let T:=leap v (packet M m 2) (0,0); have h x: ContDiff ℝ ∞ (A x):= MarkRows.polish M m _ _ ℝ _
    rw [ show settled M m v (0,0)= T-F from rfl,High.Knobs.torch_sub (M:=T) (W:=F) w ( ( h (0+v) ).sub (h 0) ) he.smooth, show torch 2 F w=0 from he.read _ (by decide), sub_zero ]; exact High.Knobs.torch_sub w ( h (0+v) ) ( h 0 ) 2

lemma responds (A:G.ColorIndex):
     HasDerivAt (fun t=> probeAct A (packet M m 2 (t,0))) ( (-8:ℂ)*(locus G:ℂ) ) t:= by
    have he(i j:Axis)(p q:FourP): HasDerivAt ( fun t=> torch 2 ( packet M m 2 (t,0)) [W i A p,W j A q] ) (torch 2 (FP (t,0)) [W i A p,W j A q]) t:=
       shear_derivative (sheared M m 2 2) _ (fun i=> Bool.noConfusion i) rfl 2 rfl (MarkRows.speed M m 2 _) _ _
    have hm: HasDerivAt (fun t=>probeAct A (packet M m 2 (t,0))) ( probeAct A (Radial.trigger M (t,0)) ) t:= HasDerivAt.fun_sum (fun i hi=> HasDerivAt.fun_sum (fun j hj=> ( ( he _ _ _ _ ).sub ( he _ _ _ _ ) ).const_smul ((1/2):ℝ)))
    rw [Radial.point_s M simple A t] at hm; convert hm using 1; unfold locus; push_cast; ring

theorem mark_money (A:G.ColorIndex) : probeAct A (settled M m v (0,0))= Tκ * (↑(v*locus G):ℂ):= by
    obtain he := difference 0 v _ _ (fun t=> responds M simple t A)
    unfold probeAct; simp_rw [ settle_bill M simple ]; unfold probeAct at he; rw [ ← Finset.sum_sub_distrib ] at he; -- sums 
    simp_rw [ ← Finset.sum_sub_distrib ] at he; convert he using 1
    · refine sum_congr rfl fun i _=> sum_congr rfl fun j _=>?_ ; module
    rw [Complex.real_smul]; push_cast; ring
end
end YM.SignedWilsonExpansion.OrderHigh
