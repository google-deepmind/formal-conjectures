import overwrite_index

def testMain : IO Unit := do
  let res1 ← replaceTag "main" "prefix<main>old</main>suffix" "new"
  if res1 != "prefix<main>new</main>suffix" then
    throw <| IO.userError s!"Test 1 failed: {res1}"

  -- Test multiple closing tags
  let res2 ← replaceTag "main" "prefix<main>old</main>suffix</main>extra" "new"
  if res2 != "prefix<main>new</main>suffix</main>extra" then
    throw <| IO.userError s!"Test 2 failed: {res2}"

  -- Test multiple opening tags
  let res3 ← replaceTag "main" "prefix<main>old<main>old</main>suffix" "new"
  if res3 != "prefix<main>new</main>suffix" then
    throw <| IO.userError s!"Test 3 failed: {res3}"

  -- Error testing
  try
    let _ ← replaceTag "main" "prefix<main>old" "new"
    throw <| IO.userError "Test 4 failed: did not throw on missing close tag"
  catch _ => pure ()

  try
    let _ ← replaceTag "main" "prefixold</main>" "new"
    throw <| IO.userError "Test 5 failed: did not throw on missing open tag"
  catch _ => pure ()

  try
    let _ ← replaceTag "main" "prefix</main>old<main>" "new"
    throw <| IO.userError "Test 6 failed: did not throw on inverted tags"
  catch _ => pure ()

  IO.println "All replaceTag tests passed!"

#eval testMain
