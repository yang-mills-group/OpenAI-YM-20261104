import YM.Contacts.Harrier.Caliber
namespace YM.Contacts.Harrier
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Kale Garf PertExtension.Series Radial Larch Ion Convoy Lumen Resetter Shuttle.Tide
open Procession Procession.Welcome Procession.Catch Procession.Sun Procession.Lotus Procession.Hinges Procession.Xenon
open Shuttle.Pigment Prairie
open scoped Classical Topology BigOperators NNReal Matrix ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}{b c d g:ℝ}{X Y A B ι κ α β: Type}{m:Side}{n k h i r l j M D:ℕ}{ζ σ:ℝ≥0}
namespace Transfer
open Parcel Prairie Planned.PrimaryIntegral295
variable {e:Parcel G} {p:Word}{s:Parcel.Step}{S:Boom} (T:e.License S ζ)(hp:OK S p)(hs:s∈S)
-- term-wise linearity; expose for other regulator observations
abbrev bring (T:Theater G) (M:ℕ)(z:Cover)(F:bore G):= T.plow M (migrated F z)
section
lemma combine (Z:Theater G)(M:ℕ)(o:Cover) {F Y:bore G}{Q}{g u:ℝ}{τ δ:ℝ≥0} {x:Dye G}(A:Z.Rich σ τ g u Q)(B:(τ:ℝ)/(Z.L.val:ℝ)≤δ)(C:Based δ x M F)(D:Based δ x M Y)(t:ℝ):bring Z M o (t • F+Y)= t • bring Z M o F+bring Z M o Y:= by
   obtain ⟨h,U,H⟩:=C; obtain ⟨hc,u,hu⟩:=D; funext i r; change bring Z M o (t • F+Y) i r=t • bring Z M o F i r+ bring Z M o Y i r; simp only [bring,Theater.plow_offset,Finset.smul_sum, ← Finset.sum_add_distrib,Pi.add_apply,Pi.smul_apply]; -- remove
   apply sum_congr rfl; intro j hj; apply sum_congr rfl; intro k hk; exact congr_fun (Theater.spot_tilt (T:=Z) A B (H.lands j k) (h.incarnate.sym j k) (hu.lands j k) (hc.incarnate.sym j k) (show i-j<dart i k from by unfold dart; omega) (show k ≤ dart i k from by unfold dart; omega) t o) r
end
-- recoil additive all arrays independent $i,r$, ingredient Rosable
lemma reco_linear (w:RodP)(F Q:House α)(c:ℝ)(p:ℕ): recoil w p (c • F+Q)= c • recoil w p F+recoil w p Q:= by
   let v:=Catch.cap p -- maybe arg
   have he (i j:ℕ)(F Q:House α): presageMark w v (c • F+Q) i j = c • presageMark w v F i j+presageMark w v Q i j:= by
      induction i using Nat.strongRecOn with| _ i ih=> simp_rw [presage_eqMark (j:=i)]; rw [show (∑ q∈Finset.range i,tickerMark w v q i • presageMark w v (c • F+Q) q j)=∑ q∈ Finset.range i,tickerMark w v q i • (c • presageMark w v F q j+presageMark w v Q q j) from Finset.sum_congr rfl fun t ht=> congr_arg _ (ih _ (Finset.mem_range.mp ht))]; simp_rw [Pi.add_apply,Pi.smul_apply,smul_add, smul_sub, Finset.smul_sum,Finset.sum_add_distrib,smul_comm c]; abel
   funext i r; simp only [recoil,Catch.swell,shift_add,shift_scale,lowerHouseMark,flipBack,Pi.smul_apply,Pi.add_apply]; split; swap; · simp
   let F':= shiftA v F; let Q':=shiftA v Q; rw [show dazzle _ = c • dazzle F'+ dazzle Q' from (show dazzle (c • F'+Q')=_ from funext fun i=> funext fun j=> by unfold dazzle; simp only [Pi.add_apply,Pi.smul_apply]; split <;> simp_all)]; apply he -- replacement
variable {v:Site s.L}{Y V:Sketch G}{x:Dye G}
include T hp hs
lemma weighs (c:ℝ)(hV:Living x M D V ζ)(hY:Living x M D Y ζ): weigh e p s M v (c • V+Y)= c • weigh e p s M v V + weigh e p s M v Y:= by
   obtain ⟨u,b,Z,h⟩:= permits e p s T hp hs; ext1 φ; exact combine _ M (curb s v) h (step_reserved ..) (hV.lineage (desk s v φ)) (hY.lineage (desk s v φ)) _
lemma weighed (hV:Living x M D V ζ): IsLinearMap ℝ (weigh e p s M v V):= by
   obtain ⟨u,b,Z,h⟩:= permits e p s T hp hs; let f:= bring (crafts e p s T hp) M (curb s v); let T':= V ∘ desk s v; have he(x y:Cards)(t:ℝ): f (T' (t • x+y))=t • f (T' x)+f (T' y):= by
      unfold T'; simp only [Function.comp_apply,(ldesk s v).map_add,(ldesk s v).map_smul,hV.lin.map_add,hV.lin.map_smul]; exact combine _ M (curb s v) h (step_reserved ..) (hV.lineage (desk s v x)) (hV.lineage (desk s v y)) t
   change IsLinearMap ℝ (fun x=> f (T' x)); constructor; · intro x y; simpa only [one_smul] using he x y 1
   have hy : f (T' 0)=0:= add_left_cancel (a:=f (T' 0)) (by simpa using! (he 0 0 1).symm); intro c x; simpa only [add_zero,hy] using he x 0 c
lemma bargain (c:ℝ)(hV:Living x M D V ζ)(hY:Living x M D Y ζ): pass e p s M v (c • V+Y)= c • pass e p s M v V + pass e p s M v Y:= by ext1 φ; unfold Transfer.pass; rw [weighs T hp hs c hV hY]; exact reco_linear ..
omit T hp hs in
lemma empty_recoil (w:RodP): recoil w M (0:House α)=0:= by have h:= reco_linear w 0 (0:House α) 1 M; apply add_left_cancel (a:=recoil w M (0:House α)); simpa only [one_smul,add_zero] using h.symm
lemma passing (hV:Living x M D V ζ): IsLinearMap ℝ (pass e p s M v V):= by
   have h:= weighed T hp hs (v:=v) hV; let F:= weigh e p s M v V; constructor
   · intro x y; unfold Transfer.pass; rw [h.map_add]; simpa only [one_smul] using reco_linear (sink e.x (e.kickoff p s)) (F x) (F y) 1 M
   intro q x; unfold Transfer.pass; rw [h.map_smul]; simpa only [add_zero,empty_recoil] using reco_linear _ (F x) 0 q M
lemma mean_tilt (h:ℕ)(c:ℝ)(hV:Living x M D V ζ)(hY:Living x M D Y ζ): Transfer.mean e p s M h (c • V+Y)=c • Transfer.mean e p s M h V+Transfer.mean e p s M h Y:= by simp_rw [Transfer.mean,bargain T hp hs c hV hY, Finset.sum_add_distrib,← Finset.smul_sum, smul_add,smul_comm c]
end Transfer
end
end YM.Contacts.Harrier
