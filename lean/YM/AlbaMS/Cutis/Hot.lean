import YM.AlbaMS.Cutis.Flare

/-!
# Witness for computation of all-order Wick on inversion orbit

Move full Rank0 Wick expectations with any F whose shift vanishes after stronger
squash test and whose rank is certified. No limit or sum assumption. Then
obtain for T.stim times products. Exact inserts in based gauge. Keep extensive
potentials never exponentiated in analysis: algebra may use Tags to isolate.
No hypothesis needed on bosonic A chosen transverse in full Ward calculus.
No assumption that weakening to Landau-gauge choice gives normalizing constants;
connection statements on normalized power-order outputs later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Cutis.Winter
open Set Function Filter LinearMap Matrix IsNilpotent
open scoped BigOperators Classical Topology Matrix InnerProductSpace
open Bric Coil Loft Inlay Inlay.Net Odom Lattice Nexus
variable {V I R S : Type*}[CommRing R]{G:Gauge} {n:Side}(T:Tune R)
variable {P:Precision.ChartRatio G}(hp:Precision.LocalRatio P)
def Area (n:Side) : LightQ G n R:= T.D (1/2) • (Rack G n P hp).stim T
def Element (G:Gauge)(n:Side):= (extoll G n T.a).replic T.D
abbrev Owner (Ω:Heave G (Arm n) (Site n) R):= T.crossT (walkT n G true) Ω
def Moves (T:Tune R)(F:LightQ G n R) := (Beam T).firm F=(Stick T).firm F
lemma Moves.product {F U:LightQ G n R}(h:Moves T F)(H:Moves T U): Moves T (F*U):=by unfold Moves at *; rw [Wire.firm_mul, Wire.firm_mul,h,H]
lemma area_move (h:Even n.val): Moves T (Area T hp n):=by unfold Moves Area; rw [map_smul,map_smul,spent _ _ h]
lemma bigBase (h:Even n.val): Owner T (Area T hp n)= (Root G P n true hp).stim T:=by unfold Area Owner; rw [map_smul]; exact ((squall G h P hp true).feels T).symm

variable [Algebra ℚ R]
private lemma moves_exp {E B I J:Type*}[Fintype E][Fintype B](A:Wire E B I J R) (F:Floor E B R)(h:IsNilpotent F): A.firm (exp F)=exp (A.firm F):= by
  let L:= Coil.bar A.fee A.stub Finset.univ; have hh:= IsNilpotent.map_exp h L -- check
  exact hh
-- rank-only transfers
lemma business (F:LightQ G n R)(h:Even n.val)(hr:FinRank F)(he:Moves T F): Fritz.eval (Element T G n).hop F= Fritz.eval (drive T).hop (Owner T F) :=by
  unfold Moves at he; rw [show Fritz.eval (Element T G n).hop F=_ from realize G n T h F hr,← he, squeeze T h F hr] -- guess guess
-- include occupation and master. normalized values separate by consumers later.
def CovPar (X:LightQ G n R) := Fritz.eval (Element T G n).hop (exp (- Area T hp n)*X)
def CovRay (X: Heave G (Foil n) (Nail n true) R):= Fritz.eval (drive T).hop (exp (- (Root G P n true hp).stim T)* X)
lemma fireCover (h:Even n.val)(X:LightQ G n R)(H:Moves T X)(he:FinRank X)(c:IsNilpotent T.z) (hk:IsNilpotent ((Rack G n P hp).stim T)):
    CovPar T hp X= CovRay T hp (Owner T X):=by
  unfold CovPar CovRay; let A:=Area T hp n; have hu:IsNilpotent (-A):= (hk.smul (T.D (1/2))).neg -- check orientation
  have hR: FinRank A:= ((Rack G n P hp).stim_rank T c).smul _; rw [business T _ h (hR.neg.exponent.mul he)]; unfold Owner; rw [Wire.crosses]; rw [Wire.firm_mul, moves_exp _ _ hu,map_neg]; rw [← bigBase T hp h,Owner,Wire.crosses] -- paths
  apply Moves.product T _ H; unfold Moves; rw [moves_exp _ _ hu,moves_exp _ _ hu, map_neg,map_neg, show (Beam _).firm A=(Stick T).firm A from area_move T hp h]
lemma RootExact (h:Even n.val)(c:IsNilpotent T.z) (hk:IsNilpotent ((Rack G n P hp).stim T))(b:Bool)
    (U: Heave G (Foil n) (Nail n true) R)(ht:Tone b U)(he:FinRank U):
    CovRay T hp (quantum T.bracket Finset.univ ((Root G P n true hp).charter T) U)=0:=by
  let S:= Root G P n true hp
  let τ:= T.D T.a⁻¹^4; let Z:= locate T hp (n:=n); let W:= S.stim T; let F:=drive T (G:=G) (n:=n)
  have hz : Z.combo+W=S.charter T:=by rw [show Z.combo= S.fair T from sincerely hp T]; exact add_sub_cancel .. -- add order
  have hW:IsNilpotent W:= by rw [show W= _ from (bigBase T hp h).symm, Owner, Wire.crosses]; exact ((hk.smul (T.D (1/2))) : IsNilpotent (Area T hp n)).map (Coil.bar _ (((Wire.register (walkT n G true)).atlas T.D).stub) _ : Floor _ _ R→ₐ[R]Floor _ _ R) -- spec
  have ht':master_eff (Z.q τ) (θ τ) Finset.univ W=0:=by
    have heq:= S.engine_master T; rw [show S.fair T=Z.combo from (sincerely hp T).symm] at heq; exact heq
  have hp' := Fritz.exacts F Z τ (Rosetta hp h T).toFund he ht (S.stim_tone T) hW (S.stim_rank T c) ht'; rw [hz] at hp'; exact hp'
end YM.MSBar.Cutis.Winter
