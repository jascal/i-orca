theory Check
  imports Certificate_Decision.Certificate_Decision_Soundness
begin

text \<open>Fails the build if any theorem of Certificate_Decision_Soundness depends on an oracle (sorry,
quick_and_dirty, evaluation), or if no theorem is found. thm_oracles prints nothing in a batch log, so the
verdict is delivered as success or failure.\<close>

ML \<open>
  let
    val thy = Context.the_global_context ();
    val prefix = "Certificate_Decision_Soundness.";
    val all = Global_Theory.all_thms_of thy true
      |> filter (fn (n, _) => String.isPrefix prefix (#1 n));
    val oracles = Thm_Deps.all_oracles (map #2 all);
    val names = map (fn ((n, _), _) => n) oracles;
  in
    if null all then error "oracle check: no theorem found (prefix mismatch?)"
    else if not (null oracles) then error ("oracle check: oracles used: " ^ commas names)
    else ()
  end
\<close>

end
