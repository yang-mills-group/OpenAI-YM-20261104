import YM.MS.Swirl.Migrate
/-!
# Decision on glyph marks Leg scaling cleared. E_Ω uses full not double N;
 the exterior geometry is supplied with `periodN` by coat callers. Continuum benchmark
 compares unscaled canonical regulator PT at each order in g.Now with same study.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Fleet
open Function Set Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Tone Frame Lattice City Latch Job Detect Tone Momentum Heat Orbit Cog Orbit.LogReal Book Convolve Program Native Wilsonian
open Draft Paint Orient Cylinder Lab Menus Fleet Puff Puff.Actors Puff.Engine Puff.Mom
open SpaceOut Swirl Swirl.Near
open scoped Topology ContDiff Interval
variable {A I W:Type}{G:Gauge}{i:I}{L:I→Side}{A':Faces I} {φ:Team}{n d:ℕ}{N:Side} {X:Actor G} {V U: W→Actor G}
    [LinearOrder W] {b: Bool} {η:I→ℝ} (c:Berth ( W:=W ) ( I:=I )) (i:I){s: Finset W} {F:Finset W→ℕ→I→ℂ}
set_option quotPrecheck false
local notation "D'"=> dimT L i
local notation "Β"=> κP G D' b
local notation "Q"=> B_init G L b ( TokenB G φ η ) i
local notation "Y"=> W0 L b (goalsK c η V) i A'
local notation "M"=> Master G (dimT L i) b
local notation "Τ"=> NRG φ (η i) ( dimT L i ) G b
local notation "Uᴛ"=> taxi ( inUse φ (η i) )
local notation "Wᴛ"=> normPay
abbrev PhysicalSum (G:Gauge)(φ:Team)(x:ℝ)(n:Side)(b: Bool)(s:Finset W)(c:W→ Cover)(A:Cover)(V:W→Actor G)(Z:T ℂ): Prop:= Endμ ( Master G n b ) σbranch ( NRG ( Stripped φ ) x n G b ) ( Font σbranch ( Marks V x n A c ) s ) Z
-- Actual definition uses absolute n FULL. recall portrait runs K(t) on dimT.
lemma σPay (he:CCOrb G η φ A' L (goalsK c η V) b F)(hv: Badge V): Endμ M σbranch Τ ( Font σbranch (ΓM c L i η A' V) s ) ( bury i s F ):= by
   have hp':= momentΓ (s:=s) c i V A' η L hv; have hu: Γ Τ σbranch:= (powerfee φ (η i)|>.1); apply ( Swirl.through (b:=b) ( S:=iota G D' ) ( riverOK BankK.pin BankK.gov ) ( «X»:=bury i s F ) hp' hu ).mpr; change Endμ M σbranch ( Β Τ ) ( Β _ ) _; rw [ ← absoluteX,← normPay ]; obtain ⟨X',Y',h,hX⟩:= he; obtain ⟨ha,H⟩:= h i; let Vp:=Y' i; let Z:= grow_θ (G:=G) b D'; let T:= CoreOrb hv b i A' c η L φ; have he : Y ∅ =0 := by funext k; change Aspect b L i A' (goalsK c η V ∅ k i)=_; rw [goals_t c η (by simp : (∅:Finset W).card≠1)]; change Aspect b L i A' 0=_; exact map_zero _;
   obtain hm:= moments Z ha H T he s; have hP : Γ Q σbranch:= by rw [ absoluteX ]; exact soldΓ hu
   have ht: Γ ( Font σbranch Y s ) σbranch:= by rw [ normPay ]; exact soldΓ hp';
   refine reg_Lη ( X:=X' i ) Z ha T.energy hm ( Cinch.totalZ (fenn Z ha H T) s (Set.mem_univ s) ) ( powerH G D' b ) hP (show Q 0=0 from ?_) ht ?_; · rw [ absoluteX ]; exact Eq.trans ( congr_arg ( readerV (iota G D') b ) ( τ_nil ( b:=b ) _ _ _ _ )) ( map_zero _ )
   intro n; exact momDepart ( fun s k=> hX s k i ) s n -- cast index Universe
lemma κglyph (hv: Badge V)(he:CCOrb G η φ A' L (goalsK c η V) b F)(hp: Badge U)(h: Changes V U φ) : PhysicalSum G φ (η i) D' b s (fun w=>c w i) ( A' i ) U ( bury i s F ):= by
   obtain hf:= σPay c i (s:=s) he hv; have hz : ( pay b • flatH G D' )= SendB G D' b ( core G 0 ):= rfl; obtain h0:= sendEven ( b:=b ) ( N:=D' ) ( crisp G 0 ); obtain ht:= memBill ( b:=b ) ( N:=D' ) ( crisp G 0 ) ( participates G 0 ); rw [ ← hz ] at h0 ht; let Z:= φ;
   obtain ⟨hV,hg⟩:= powerfee ( G:=G ) ( b:=b ) ( N:=D' ) ( Stripped φ ) ( η i ); apply ( ready_η ( zeroM b ) (paySym b) ( feeDown φ ( η i ) ) (excavate G D' φ ( η i )) ( guise φ (η i)) ht h0 μτrank hg hV ( τ_nil .. ) ( momentΓ c i U A' η L hp (s:=s) ) ).mpr; rw [ ← βalign, ← Near.translate c i h ]; exact hf
-- unit tests at ∅. all. independent kernel data in finite formula by standard ∑ power bounded support.
end YM.MS.Fleet
