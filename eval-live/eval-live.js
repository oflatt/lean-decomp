/**
 * Render evaluation tables into a container element.
 * @param {HTMLElement|string} container - DOM element or element ID
 * @param {Object} data - Dict of table name -> array of row objects
 * @param {string} [name] - Project name shown in the heading
 * @param {string} [graphScript] - Python script using eval_live decorators
 * @param {string} [evalLivePy] - Source of the eval_live.py library
 */
function initEvalLive(container, data, name, graphScript, evalLivePy) {
  if (typeof container === "string") {
    container = document.getElementById(container);
  }
  container.classList.add("eval-live");
  container.innerHTML = "";

  if (name) {
    const h1 = document.createElement("h1");
    h1.className = "eval-live-title";
    h1.textContent = name + " \u2014 Eval Live";
    container.appendChild(h1);
  }

  // Graphs section (populated async if graphScript provided)
  if (graphScript && evalLivePy) {
    const graphSection = document.createElement("div");
    graphSection.className = "graph-section";
    const graphStatus = document.createElement("div");
    graphStatus.className = "graph-status";
    graphStatus.textContent = "Loading Pyodide...";
    graphSection.appendChild(graphStatus);
    container.appendChild(graphSection);

    runGraphs(graphSection, graphStatus, data, graphScript, evalLivePy);
  }

  for (const [tableName, rows] of Object.entries(data)) {
    if (!Array.isArray(rows) || rows.length === 0) continue;

    const section = document.createElement("div");
    section.className = "table-section";

    const heading = document.createElement("h2");
    heading.textContent = tableName;
    const rowCount = document.createElement("span");
    rowCount.className = "row-count";
    rowCount.textContent = `(${rows.length} rows)`;
    heading.appendChild(rowCount);
    section.appendChild(heading);

    const cols = [...new Set(rows.flatMap(Object.keys))];

    const table = document.createElement("table");

    const thead = document.createElement("thead");
    const headerRow = document.createElement("tr");
    // Expand column header
    const thExpand = document.createElement("th");
    thExpand.className = "expand-col";
    headerRow.appendChild(thExpand);
    for (const col of cols) {
      const th = document.createElement("th");
      th.textContent = col;
      headerRow.appendChild(th);
    }
    thead.appendChild(headerRow);

    // Filter row
    const filterRow = document.createElement("tr");
    filterRow.className = "filter-row";
    const filterExpandTh = document.createElement("th");
    filterExpandTh.className = "expand-col";
    filterRow.appendChild(filterExpandTh);
    const filters = [];
    for (const col of cols) {
      const th = document.createElement("th");
      const input = document.createElement("input");
      input.type = "text";
      input.className = "filter-input";
      input.placeholder = "filter...";
      filters.push({ col, input });
      th.appendChild(input);
      filterRow.appendChild(th);
    }
    thead.appendChild(filterRow);
    table.appendChild(thead);

    const tbody = document.createElement("tbody");
    const rowEls = [];
    for (const row of rows) {
      const tr = document.createElement("tr");
      tr.classList.add("collapsed");

      const tdBtn = document.createElement("td");
      tdBtn.className = "expand-col";
      const btn = document.createElement("button");
      btn.className = "expand-btn";
      btn.textContent = "+";
      btn.addEventListener("click", () => {
        const collapsed = tr.classList.toggle("collapsed");
        btn.textContent = collapsed ? "+" : "\u2212";
      });
      tdBtn.appendChild(btn);
      tr.appendChild(tdBtn);

      for (const col of cols) {
        const td = document.createElement("td");
        const val = row[col];
        td.textContent = val === undefined ? "" : typeof val === "object" ? JSON.stringify(val) : String(val);
        tr.appendChild(td);
      }
      tbody.appendChild(tr);
      rowEls.push({ tr, row });
    }

    function applyFilters() {
      let visible = 0;
      for (const { tr, row } of rowEls) {
        let show = true;
        for (const { col, input } of filters) {
          const query = input.value.toLowerCase();
          if (!query) continue;
          const val = row[col];
          const text = val === undefined ? "" : typeof val === "object" ? JSON.stringify(val) : String(val);
          if (!text.toLowerCase().includes(query)) {
            show = false;
            break;
          }
        }
        tr.style.display = show ? "" : "none";
        if (show) visible++;
      }
      rowCount.textContent = `(${visible}/${rows.length} rows)`;
    }
    for (const { input } of filters) {
      input.addEventListener("input", applyFilters);
    }
    table.appendChild(tbody);

    const wrap = document.createElement("div");
    wrap.className = "table-wrap";
    wrap.appendChild(table);
    section.appendChild(wrap);
    container.appendChild(section);
  }
}

async function runGraphs(section, status, data, graphScript, evalLivePy) {
  try {
    const pyodide = await loadPyodide();
    status.textContent = "Installing matplotlib...";
    await pyodide.loadPackage("matplotlib");
    status.textContent = "Running graph script...";

    // Register the eval_live module
    pyodide.FS.writeFile("/home/pyodide/eval_live.py", evalLivePy);

    // Run the user script then call run_graphs(data)
    await pyodide.runPythonAsync(graphScript);
    pyodide.globals.set("__eval_live_data__", pyodide.toPy(data));
    const resultProxy = await pyodide.runPythonAsync(
      "from eval_live import run_graphs; run_graphs(__eval_live_data__)"
    );
    const graphs = resultProxy.toJs({ create_proxies: false });
    resultProxy.destroy();

    status.textContent = "";
    if (!graphs || graphs.length === 0) {
      status.textContent = "No graphs registered.";
      return;
    }

    // Button bar
    const bar = document.createElement("div");
    bar.className = "graph-bar";
    section.appendChild(bar);

    // Display area
    const display = document.createElement("div");
    display.className = "graph-display";
    section.appendChild(display);

    for (const g of graphs) {
      const name = g.get("name");
      const src = g.get("src");

      const btn = document.createElement("button");
      btn.className = "graph-btn";
      btn.textContent = name;
      btn.addEventListener("click", () => {
        // Toggle active state
        for (const b of bar.querySelectorAll(".graph-btn")) b.classList.remove("active");
        btn.classList.add("active");
        display.innerHTML = "";
        const img = document.createElement("img");
        img.src = src;
        img.alt = name;
        display.appendChild(img);
      });
      bar.appendChild(btn);
    }

    // Show first graph by default
    bar.querySelector(".graph-btn").click();
  } catch (err) {
    status.textContent = "Graph error: " + err.message;
    console.error(err);
  }
}
