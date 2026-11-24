import YM.SignedWilsonExpansion.F9.Fetch
/-!
# Boundary-point inverse

A rank-filtered real solve for EACH registered scalar (entry clock as produced).
No use of any approximation on new marked qlocal inputs. The numerical map
remains in honest bare perturbative coefficients; this solve determines WHOLE
tensors to every strictly earlier rank at active orders. Keep common choices
indexed by h and order on one reserved Report epoch. Apply to the actual P̂
at the top word (after price is restored at epoch change).
-/
set_option autoImplicit false
set_option maxHeartbeats 750000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Gauge AnalyticNext.QuarticMatch.Sheets Filter Function Matrix Lattice RG Laurent Bloch Metric
open Blue FreeResolvent Work.F08 Bank Soil Exterior Next.Free Tree Precision Power Embroider
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb
open Realm Fountain PathCost Embroider.Canvas Shard PowerSeries
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{A:Levels G}{Ñ:ChartRatio G}{h p k m c N u e i j l r q d:ℕ}{F:Labels.Frame G h}{H:Hol G} {Q:SectionData F}
variable {B M X Y z:ℝ}{P:SourceP F}{U:Type*}{E W:Credit}{R:Realm G (q+1) E}

lemma silent (G:Gauge) (k:ℕ): Auth k (0:Era G ℝ):=by let S:Unit→ Era G ℝ:= fun _=>0; simpa using Auth.sum (k:=k) (P:=S) (S:=∅) (by simp)
lemma pier_μ (g:G.Simple)(q:LocalRatio Ñ)(v:m≤c)(hp:c≤N){P:Era G ℝ}(hP:Auth k P)(a:ℝ): pier A Ñ N h k c m (a•P)=a•pier A Ñ N h k c m P:= by simpa only [Finset.sum_singleton] using pier_sum (h:=h) (A:=A) g q v hp {()} (fun _=>a) (fun _=>P) (fun i _=>hP)
lemma pier_nil (g:G.Simple)(q:LocalRatio Ñ)(v:m≤c)(hp:c≤N): pier A Ñ N h k c m 0=0:=by
    have he:= pier_sub (h:=h) (A:=A) g q v hp (silent G k) (silent G k); simpa only [sub_self] using he
-- packaged linear finite-dimensional probe. unit stays visible.
def output (F:Frame G h)(d:ℕ)(P:Era G ℝ): BankP F d:= fun i=>row F (P.2 i.2.val (wr F i.1)) ⟨i.1,rfl⟩
lemma output_at {i:TagIx F r}(Y: Era G ℝ)(p:e≤q): row F (Y.2 e r) i= output F q Y (eyeTag F e q p i):=by obtain ⟨i,hv⟩:= i; subst r; rfl
lemma output_plus {P Q:Era G ℝ}(p:Auth k P)(q:Auth k Q):output F d (P+Q)=output F d P+output F d Q:= funext fun i=> axPlus p q ⟨i.1,rfl⟩
lemma output_nil: output F d 0=0:= funext fun i=>row_nil F ⟨i.1,rfl⟩
lemma output_μ (Y:Era G ℝ)(a:ℝ): output F d (a • Y)=a • output F d Y:= funext fun i=>row_μ F _ a ⟨i.1,rfl⟩
lemma rack_plus (F:Frame G h)(P:SourceP F)(x y: BankP F p): rack F P (x+y)=rack F P x + rack F P y:=by unfold rack; simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
lemma rack_μ (F:Frame G h)(P:SourceP F)(t:ℝ)(x:BankP F p):rack F P (t•x)=t•rack F P x:=by unfold rack; simp only [Pi.smul_apply,smul_assoc,Finset.smul_sum]
lemma rack_nil (F:Frame G h)(P:SourceP F)(p:ℕ):rack F P (0:BankP F p)=0:=by simp [rack]

-- all clocks in output local at measurement stand (through f). No tuning.
def heard (F: Frame G h)(A:Levels G)(Ñ:ChartRatio G)(k N p c m:ℕ)(P:Era G ℝ): BankP F p:=output F p (pier A Ñ N h k c m P)
def lap (p:Palette F P k u q X) (v:Chartage Q A Ñ m c N k u q X): BankP F q →ₗ[ℝ] BankP F q where
    toFun x:= heard F A Ñ k N q c m (rack F P x)
    map_add' x y:= by
       unfold heard; rw [rack_plus,pier_add v.simple v.ratios v.length v.cap (p.mix x) (p.mix y)]; exact output_plus (piered v.simple v.ratios v.length v.cap (p.mix x)) (piered v.simple v.ratios v.length v.cap (p.mix y))
    map_smul' c x:=by unfold heard; rw [rack_μ,pier_μ v.simple v.ratios v.length v.cap (p.mix x),output_μ]; rfl
lemma listening (p:Palette F P k u q X) (v:Chartage Q A Ñ m c N k u q X) (x: BankP F q){Y:Era G ℝ}(hY: Auth k Y) : heard F A Ñ k N q c m (Y+rack F P x)= heard F A Ñ k N q c m Y+lap p v x:=by unfold heard; rw [pier_add v.simple v.ratios v.length v.cap hY (p.mix x)]; exact output_plus (piered v.simple v.ratios v.length v.cap hY) (piered v.simple v.ratios v.length v.cap (p.mix x))
abbrev Enough (F:Frame G h)(p u k:ℕ): Credit:= (billed F p u k).choose
lemma prepaid_solve (p:Palette F P k u q X) (v:Chartage Q A Ñ m c N k u q X)(x: BankP F q){Y:Era G ℝ}(hY: Auth k Y)(hm:0≤ M)(y:∀ e≤q,∀ r,Fruit 0 1 u (Y.2 e r) M)(f:∀ i, ‖heard F A Ñ k N q c m (Y+rack F P x) i‖≤ M) : (∀ i,‖x i‖ ≤ (Enough F q u k).buy X * M) ∧ ∀ j, m≤ j → j≤c → ∀ e≤ q, ∀ r,Fruit 0 1 u ((pier A Ñ N h k c j (Y+rack F P x)).2 e r) ((Enough F q u k).buy X*M):=by
    have hU e (p':e≤q) r:= (billed F q u k).choose_spec e p' r Q A Ñ m c N M X P Y x q 0 le_rfl (by unfold When; omega) hm p hY v (fun i j e=>y i (by unfold When at e; omega) j) (fun i j e v=> by rw [output_at _ (show i≤ q from by unfold When at e; omega)]; exact f _) -- goal cast issues
    refine ⟨?_,fun j hj h e p r=> (hU e p r).1 j hj h⟩; rintro ⟨i,k⟩; exact (hU k.val (Nat.le_of_lt_succ k.isLt) (wr F i)).2 (Nat.le_of_lt_succ k.isLt) ⟨i,rfl⟩
lemma lap_bijective (p:Palette F P k u q X) (v:Chartage Q A Ñ m c N k u q X): Bijective (lap p v):=by
    let L:=lap p v
    have h (x: BankP F q)(hx:L x=0):x=0:=by
       have he i : ‖heard F A Ñ k N q c m ((0:Era G ℝ)+rack F P x) i‖≤ 0:=by rw [zero_add,show heard _ _ _ _ _ _ _ _ _=0 from hx]; exact norm_zero.le
       funext i; have he:= (prepaid_solve p v x (silent G k) le_rfl (fun _ _ _=> Fruit.zero) he).1 i; rw [mul_zero] at he; exact norm_le_zero_iff.mp he
    have hc: Injective L:=fun a b hx'=> sub_eq_zero.mp (h _ (by rw [map_sub,hx',sub_self])); exact ⟨hc,LinearMap.surjective_of_injective hc⟩

/-- Boundary solver. Needs actual chartage and actually admissible cover palette; output values *bottom local*.
Use proof irrelevance and uniqueness at every h and q, not different fitted
field names for differing `u`. -/
def solve (p:Palette F P k u q X)(v:Chartage Q A Ñ m c N k u q X)(Y:Era G ℝ)(M:BankP F q): BankP F q:= (LinearEquiv.ofBijective (lap p v) (lap_bijective p v)).symm (M-heard F A Ñ k N q c m Y)
lemma solve_target (p:Palette F P k u q X) (v:Chartage Q A Ñ m c N k u q X) (M:BankP F q){Y:Era G ℝ}(hY:Auth k Y): heard F A Ñ k N q c m (Y+rack F P (solve p v Y M))= M:=by
    rw [listening p v _ hY]; let L:=LinearEquiv.ofBijective (lap p v) (lap_bijective p v); change heard F A Ñ k N q c m Y+ L (L.symm (M-_))=M; rw [L.apply_symm_apply, add_comm]; simp
lemma solve_unique (p:Palette F P k u q X) (v:Chartage Q A Ñ m c N k u q X) {x M:BankP F q}{Y: Era G ℝ}(hY:Auth k Y)(he:heard F A Ñ k N q c m (Y+rack F P x)=M): x=solve p v Y M:=by
    apply (lap_bijective p v).1; apply add_left_cancel (a:=heard F A Ñ k N q c m Y); rw [←listening p v _ hY, ←listening p v _ hY,he,solve_target p v _ hY]
lemma solve_bounds (p:Palette F P k u q X) (v:Chartage Q A Ñ m c N k u q X)(x:BankP F q){Y:Era G ℝ}(hY:Auth k Y) {M:ℝ}(hm:0≤M)(y:∀ e≤q,∀ r,Fruit 0 1 u (Y.2 e r) M)(f:∀ i, ‖x i‖≤ M) :
    let a:=solve p v Y x; (∀i, ‖a i‖ ≤ (Enough F q u k).buy X*M) ∧ ∀ j,m≤ j→j≤c→∀ e≤q,∀ r, Fruit 0 1 u ((pier A Ñ N h k c j (Y+rack F P a)).2 e r) ((Enough F q u k).buy X*M):=by intro a; exact prepaid_solve p v _ hY hm y (fun i=>by rw [solve_target p v _ hY]; exact f _)
end YM.WilsonCoeffUV.Mer.Xa
