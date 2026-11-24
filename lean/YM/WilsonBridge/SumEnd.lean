import YM.WilsonBridge.Transverse
import YM.WilsonBridge.TreeBridge
/-!
# Exact ambient response, same coupling and vacuum series

Uses Φ for effective channels and then the actual Γ.finite graded Gauge End.
Independent of positive mark provenance except stated support. Next theorem instantiates
on concrete physical channels to compute inserted coefficients in terms of Orb.diag.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBridge
open MS MS.Book MS.Koszul MS.Swirl MS.Puff MS.Cylinder MS.Orbit
open MS.Book.Convolve Program Puff.Mom Puff.Engine Puff.SplitP Puff.Actors Puff.Dynamics Orbit.LogReal Orbit.Cog
open Function Finset
open scoped BigOperators
variable {A K X E : Type}[Fintype A][Fintype K]{p:Sector A}{r:Sector K}
    [AddCommGroup E][Module ℂ E]
local notation "δ"=> useN.refineV
lemma reprice (c:Cn)(z:E): substitute c (δ z)= δ z:= by
    funext i; cases i with
    | zero=> exact Program.pay0 c _
    | succ i=>
        rw [rules]; unfold SplitP.refineV; rw [if_neg (show i+1≠ useN.origin from Nat.succ_ne_zero _) ]; apply Finset.sum_eq_zero; intro x hx; split_ifs with h; · rw [show x=0 from h, Program.cut,pow_zero, PowerSeries.coeff_one, if_neg (show i+1≠0 by omega),zero_smul]
        rw [smul_zero]
omit [Fintype A] in
lemma note_sub (U:Submodule ℂ E){V:T E}(c:Cn)(h:V∈ allIndex U ℕ): substitute c V∈ allIndex U ℕ:= by intro i _; rw [rules]; exact U.sum_mem fun j _=> U.smul_mem _ ( h j (Set.mem_univ _) )
variable {c:Cn}{Q V:SpecB A}
omit [Fintype A] in
lemma cexp (h:Rooted c)(p:Sector A)(hz:Q 0=0): exp0 p (substitute c Q)= substitute c (exp0 p Q):= by
    let M:= PermV p; let e := substitute c ( P:=Raw A ℂ ); have ht: Tether e M M:= ⟨ reprice (E:=Raw A ℂ) c ((actor p).unit),fun F G=> (substitute_pair h F G ( product p )).symm⟩
    have hy : ∀ (k:ℕ), (actor p|>.stack useN).cheers (e Q) k = e (M.cheers Q k):= fun k=> (ht.cheersV k Q).symm
    funext i; change _= e _ i; unfold exp0 Cheer; rw [hy]; simp_rw [e,rules]; refine Finset.sum_congr rfl (fun j hj=>?_); congr 1; exact overbook (actor p) useN Q hz (Finset.mem_Iic.mp hj)
local infixl:70 " ⚘ " => Trunk.core
lemma migrate (c₀:Rooted c)(B:Grain A){Z:T ℂ}(h:Endμ B p Q V Z)(hz:Q 0=0): Endμ B p (substitute c Q) (substitute c V) (substitute c Z) := by
    change promote (View B) ( pairW (product p) ( exp0 p _ ) _ )=_; unfold Endμ at h; rw [ cexp c₀ p hz, substitute_pair c₀, Program.comm ]; change substitute c ( ℶV B ( (PermV p).core (exp0 p Q) V ) )= pairW Toy.core ( promote (View B) ( substitute c (exp0 p Q)) ) ( substitute c Z ); rw [h, Program.comm,substitute_pair c₀ ]; rfl
omit [Fintype A] in
lemma relative_promote (Q:SpecB A)(i:ℕ): FreeBV.relative Q i= if i=0 then 0 else Q i:= by rw [FreeBV.relative,Pi.sub_apply]; unfold SplitP.refineV; split_ifs with h h' hc <;> first| contradiction | simp [ show i=0 from h ]| rw [sub_zero]
omit [Fintype K] in
lemma supported_pull (U:Matrix K A ℂ) (h:Tie p r (fun i j=>U i j)) (hv: Γ V p): Γ (promote (pull U) V) r:= by intro i _; rw [promised]; obtain ⟨he,k,hk⟩:= fee_spec (hv i (Set.mem_univ _)); exact ⟨pull_symm U h he,minH ( pull_limit U hk )⟩
omit [Fintype K] in
lemma pLevel (U:Matrix K A ℂ)(Q:Raw A ℂ) (n:ℤ): promote (pull U) (rankLevel n Q)=rankLevel n (pull U Q):= funext fun _=> pull_mask ..
-- general relative lemma
omit [Fintype K] in
lemma relative_slot (U:Matrix K A ℂ) (Q:SpecB A): promote (pull U) ( FreeBV.relative Q )= FreeBV.relative (promote (pull U) Q):= by funext i; rw [promised,relative_promote Q,relative_promote ( promote (pull U) Q )]; split; exact map_zero _; rfl
omit [Fintype A] in
lemma variant (Q:SpecB A) : substitute c ( FreeBV.relative Q )= FreeBV.relative ( substitute c Q ):= by unfold FreeBV.relative; rw [map_sub,reprice,Program.pay0 c]
namespace PeriodicEnd
open Lattice Full Injections Based Based.Position Plane City Tone Native Native.Wilsonian MS.Fleet FreeBV Near
variable {G:Gauge}{n:Side}
local notation "R" => Position.Letter G n
local notation "Y" => Full.Index G n
local notation "φ"=> σbranch ( G:=G ) ( n:=n )
local notation "π"=> Position.Parity G n
local notation "Qreg"=> interaction ( Position.actionW G n ) ( Position.haarW G n )
local notation "Top"=> promote ( ( (2:ℂ)⁻¹ ) • Lab.docket ( A:=BH G ) ( «R»:=ℂ ) n )
local notation "Θp"=> promote ( pull ( Θ G n ) )
local notation "Uv"=> promote ( pull ( Ux G n ) )
local notation "Fv"=> promote ( pull ( Full.GU G n ) )
local notation "Mv"=> Master G n true
local infixl:70 " ⋆ " => product π
variable (t:Team)(x:ℝ)
local notation "Rt"=> style G ( Stripped t ) x
local notation "qk"=> NRG ( Stripped t ) x n G true
abbrev staged (G:Gauge)(n:Side)(X:T (Dot G Cover)): SpecB (Full.Index G n):= relative ((promote ( ((2:ℂ)⁻¹) • Lab.docket ( A:=BH G ) ( «R»:=ℂ ) n )) X)
local notation "Pz"=>staged G n
-- actual coupling from Team; law real unit
local notation "Sh"=> substitute ( Book.Program.shift t x )
lemma stages : NRG t x n G true= Fv ( Pz (style G t x) ):= by
    funext i; unfold NRG; by_cases hi:i=0; · rw [if_pos hi,promised,staged,relative_promote,if_pos hi,map_zero]
    rw [ promised,staged,relative_promote, if_neg hi,promised, LinearMap.smul_apply, if_neg hi ]; exact FiniteDFT.sendBulk ( H:=style G t x i ) true -- defeq? pay true def
lemma Γ_t (B:SpecB Y) (h:Γ ( Fv B ) φ): Γ B φ:= by
    let U:= FiniteDFT.Fx (BH G) n; have hu : Tie φ φ (fun i j=> U i j):= by intro i j he; change scaleZ n*FiniteDFT.F _ _ j ( i.1,-i.2 )≠0 at he; exact FiniteDFT.tie_fwd Landau.parity ( i.1,-i.2 ) j ( right_ne_zero_of_mul he )
    rw [show B=promote (pull U) ( Fv B ) from ?_]; exact supported_pull U hu h
    funext i; rw [promised,promised,pull_comp, show U*Full.GU G n=1 from FiniteDFT.fwd_inv ..,pull_id]
lemma Γ_top : Γ ( Pz (style G t x)) φ:= Γ_t _ (by rw [ ← stages ]; exact ( Near.powerfee t x ).1 )
lemma positionOrder (A:SpecB Y) (hA:Γ A φ)(Z) : Endμ (Master G n true) φ (NRG t x n G true) (Fv A) Z ↔ Endμ (HalfF G n true) φ ( Pz (style G t x) ) A Z:= by rw [stages]; exact pull_end _ _ _ rfl (Γ_top t x) hA (FiniteDFT.tie_fwd Landau.parity) Z
-- full to projected. interaction exact before loop.
lemma paintOrder (he:Even n.val) : Θp (Uv ( Top (Native.Wilsonian.core G)))= Θp (FreeBV.action ( Position.actionW G n ) ( Position.haarW G n ) ):= by
    have hb (r:ℤ)(A:Dot G Cover): promote (Lab.docket n) (Book.levels r A)= rankLevel r ( Lab.docket n A ):= level_up r A n true -- dots
    funext k; simp_rw [ Native.Wilsonian.core, FreeBV.action,map_add,Pi.add_apply,promised ]; -- inspect
    simp_rw [ LinearMap.smul_apply, show ∀ r:ℤ,∀ A:Dot G Cover, Lab.docket n (Book.levels r A k)= _ from fun r A=> congr_fun (hb r A) k, rankLevel, map_smul, pull_mask, wholeU he,haarU he,map_smul,checked_p he ]; norm_num [ smul_smul ]
lemma rec_p (he:Even n.val): Θp (Uv ( Pz Rt ))= Θp (Sh Qreg):= by
    unfold staged; rw [relative_slot,relative_slot, interaction, variant (c:=shift t x),relative_slot]; unfold style; rw [ Near.strip_wobble ]; simp_rw [Program.comm]; rw [ paintOrder he ]
-- generic mark. field Γ. normalization both actions and resolutions.
variable (he:Even n.val)
local notation "FL" => Based.Kinetics.Fixing.half ( landauBasis G he )
local notation "Γp"=> Pz Rt
-- pull reindexed. for *all* marked alphabet (Θ here explicit so no provenance assumptions on A)
lemma responseOrder (A:SpecB Y)(hA:Γ A φ)(Z) : Endμ Mv φ qk (Fv A) Z ↔ Endμ FL π (Sh Qreg) (Uv A) Z:= by
   have hA' := supported_pull _ Injections.transports hA
   have hu := Γ_top (G:=G) (n:=n) ( Stripped t ) x
   have hv : Γ (Sh Qreg) π:= note_sub (FeeP π) ( shift t x ) master.supported -- expose
   rw [ positionOrder (n:=n) _ _ A hA ]; calc
      _ ↔ Endμ FL π ( Uv Γp ) ( Uv A ) Z := Iff.symm (pull_end _ _ _ (charge_push he) hu hA transports _)
      _ ↔ Endμ FL π ( Θp ( Uv Γp ) ) ( Θp ( Uv A ) ) Z := Iff.symm (pull_end _ _ _ (firms he) ( supported_pull _ transports hu ) hA' projection_tie _ )
      _ ↔ Endμ FL π ( Θp ( Sh Qreg ) ) ( Θp ( Uv A ) ) Z := by rw [ rec_p t x he ]
      _ ↔ _:= pull_end _ _ _ (firms he) hv hA' projection_tie _
-- scalar vacuum though End on unmarked is unit, actual stronger equality before division
lemma vacuum_atomic : ℶV Mv ( exp0 φ qk )= Sh ( ℶV FL ( exp0 π Qreg ) ):= by
   have hu := Γ_top ( G:=G ) ( n:=n ) ( Stripped t ) x; have hz:= supported_pull _ Injections.transports hu
   have ha : Γ (Sh Qreg) π:= note_sub (FeeP π) _ master.supported
   rw [ stages ]; calc
      _ = ℶV (HalfF G n true) ( exp0 φ Γp ):= by rw [ show exp0 φ ( Fv _ )= pointL ℕ (pull (GU G n)) ( exp0 φ Γp ) from (pull_exp _ (FiniteDFT.tie_fwd Landau.parity) _).symm ]; exact shade_view _ rfl (expΓ hu)
      _= ℶV FL ( exp0 π ( Uv Γp ) ):= by rw [ show exp0 π ( Uv _ )= pointL ℕ (pull (Ux G n)) ( exp0 φ Γp ) from (pull_exp _ transports _).symm ]; exact ( shade_view _ (charge_push he) (expΓ hu) ).symm
      _= ℶV FL (exp0 π (Θp (Uv Γp) ) ):= by rw [ show exp0 π ( Θp (Uv _) )=pointL ℕ (pull (Θ G n)) ( exp0 π (Uv Γp) ) from (pull_exp _ projection_tie _).symm ]; exact (shade_view _ (firms he) (expΓ hz)).symm
      _= ℶV FL (exp0 π (Sh Qreg)):= by rw [ rec_p t x he, show exp0 π ( Θp ( Sh Qreg ) )= pointL ℕ (pull (Θ G n)) ( exp0 π (Sh Qreg) ) from (pull_exp _ projection_tie _).symm ]; exact shade_view _ (firms he) (expΓ ha)
      _ = _:= by rw [ cexp (Program.share t x) π MasterLaw.initial_zero ]; exact Program.comm ..
local notation "CR"=> EndRule.response π FL (Sh Qreg)
lemma actor_response (A:SpecB Y) (hA:Γ A φ) : Endμ Mv φ qk (Fv A) ( CR (Uv A) ):= ( responseOrder t x he A hA _ ).mpr (EndRule.agrees π FL (Sh Qreg) ((Program.pay0 (shift t x) Qreg).trans MasterLaw.initial_zero ) _ )
lemma tree_response (O:Wilson.Config G n→ℝ) (ho:Position.Invariant O)(hs:Taylor.germ (Position.charted O))(d:ℕ)(hf:From (Position.insertion O) d): CR ( Sh ( rankLevel d (Position.insertion O)))= Sh (fun n=>( PertExtension.Orb.diag (PertExtension.Orb.restrictedO O) (n+d) :ℂ )):= by
    let U:= Position.insertion O; apply EndRule.unique π FL ( Sh Qreg ) (Sh (rankLevel d U)) ((Program.pay0 (shift t x) Qreg).trans MasterLaw.initial_zero); exact migrate ( Program.share .. ) _ ( Position.tree_to_based he O d (landauBasis G he) hs ho hf ) MasterLaw.initial_zero
end PeriodicEnd
end YM.WilsonBridge
