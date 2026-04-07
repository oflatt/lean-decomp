/**
 * Render evaluation tables into a container element.
 * @param {HTMLElement|string} container - DOM element or element ID
 * @param {Object} data - Dict of table name -> array of row objects
 * @param {string} [name] - Project name shown in the heading
 */
function initEvalLive(container, data, name) {
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
